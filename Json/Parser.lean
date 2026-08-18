/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Json.Spec

public section

namespace Json

/-!
Reading text into a value.

`parse` takes a `String` and `parseBytes` a `ByteArray`, which is where the UTF-8 that RFC 8259
requires is enforced, by the verified decoder in `Init.Data.String.Decode`. Text that is not one
complete value is an error rather than a partial value, and an error says what was wrong and
where.

The defaults are the strict readings, and none of them is a crash guard, the machine keeping its
stack on the heap: a repeated field name is refused, nesting beyond 1024 is refused, and a
significand of more than a thousand digits is refused unread. `Config` turns off any of the
three. What no configuration relaxes is the refusal of a lone surrogate, which denotes no
sequence of code points at all.
-/

/-- What to do when an object names the same field twice. -/
inductive DuplicateKeys where
  | reject
  | allow
deriving DecidableEq, Repr

/-- How strictly to read. Every default here is the strict reading. -/
structure Config where
  /--
  Rejecting is the default because the RFC leaves the outcome unspecified, so accepting exposes
  the difference between two implementations reading the same bytes.
  -/
  duplicateKeys : DuplicateKeys := .reject
  /--
  A limit on nesting, as policy rather than as protection: the parser keeps its work on the heap,
  so `none` is safe and bounded only by memory.
  -/
  maxDepth : Option Nat := some 1024
  /--
  A limit on the digits of a significand or an exponent. `none` is permitted, at the cost of a
  quadratic conversion, since a mantissa is built a digit at a time.
  -/
  maxNumberDigits : Option Nat := some 1000
  /-- RFC 8259 permits ignoring a leading `U+FEFF` in text that was not networked. -/
  ignoreBOM : Bool := true
deriving Repr

/-- Why a text was refused. `describe` renders one as a sentence. -/
inductive ErrorKind where
  | unexpectedEnd
  | unexpectedChar (c : Char)
  | trailingText (c : Char)
  | controlCharInString (c : Char)
  | unknownEscape (c : Char)
  | badHexEscape
  | loneSurrogate
  | expectedDigit
  | duplicateKey (name : String)
  | depthExceeded
  | tooManyDigits
  | invalidUtf8
deriving DecidableEq, Repr

/-- A failure, with the character offset at which it was detected. -/
structure Error where
  position : Nat
  kind : ErrorKind
deriving DecidableEq, Repr

/-- A description fit for a user, rather than the constructor's `Repr`. -/
def ErrorKind.describe : ErrorKind → String
  | unexpectedEnd => "unexpected end of input"
  | unexpectedChar c => s!"unexpected character {repr c}"
  | trailingText c => s!"unexpected text after the value, starting with {repr c}"
  | controlCharInString c =>
    s!"a string holds the control character {repr c}, which has to be escaped"
  | unknownEscape c => s!"unknown escape \\{c}"
  | badHexEscape => "a \\u escape needs four hexadecimal digits"
  | loneSurrogate => "a \\u escape denotes half of a surrogate pair, with no partner beside it"
  | expectedDigit => "expected a digit"
  -- A field name arrives from the input, so a long one is not repeated back.
  | duplicateKey name =>
    if name.length ≤ 40 then s!"the field name {repr name} appears twice"
    else "a field name appears twice"
  | depthExceeded => "nesting deeper than the configured limit"
  | tooManyDigits => "a number with more digits than the configured limit"
  | invalidUtf8 => "the input is not valid UTF-8"

instance : ToString ErrorKind := ⟨ErrorKind.describe⟩

instance : ToString Error := ⟨fun e => s!"{e.kind.describe} at character {e.position}"⟩

namespace Parser

/--
A scan that consumed at least one character of `input`. Carrying the proof here rather than
proving it afterwards keeps the machine's termination argument to one line per call.
-/
structure Scanned (α : Type) (input : List Char) where
  value : α
  rest : List Char
  pos : Nat
  consumed : rest.length < input.length

/-! ## Leaf scanners -/

/-- A scan that may have consumed nothing, as whitespace and the optional productions can. -/
structure Consumed (α : Type) (input : List Char) where
  value : α
  rest : List Char
  pos : Nat
  notLonger : rest.length ≤ input.length

def skipWs (input : List Char) (pos : Nat) : Consumed Unit input :=
  match input with
  | c :: rest =>
    if Spec.isWs c then
      let r := skipWs rest (pos + 1)
      ⟨(), r.rest, r.pos, by have := r.notLonger; simp; omega⟩
    else
      ⟨(), c :: rest, pos, by simp⟩
  | [] => ⟨(), [], pos, by simp⟩

/-- `4HEXDIG`, taken as four characters so that the caller consumes them by pattern. -/
def hex4? (c₁ c₂ c₃ c₄ : Char) : Option Nat :=
  match Spec.hexVal? c₁, Spec.hexVal? c₂, Spec.hexVal? c₃, Spec.hexVal? c₄ with
  | some v₁, some v₂, some v₃, some v₄ => some (v₁ * 4096 + v₂ * 256 + v₃ * 16 + v₄)
  | _, _, _, _ => none

/-- The two-character escapes, which do not include `u`. -/
def escapeChar? (c : Char) : Option Char :=
  if c == '"' then some '"'
  else if c == '\\' then some '\\'
  else if c == '/' then some '/'
  else if c == 'b' then some '\x08'
  else if c == 'f' then some '\x0c'
  else if c == 'n' then some '\n'
  else if c == 'r' then some '\x0d'
  else if c == 't' then some '\t'
  else none

/-- A code point that is neither a surrogate nor out of range. -/
def charOfCodePoint? (v : Nat) : Option Char :=
  if h : (UInt32.ofNat v).isValidChar then some ⟨UInt32.ofNat v, h⟩ else none

def combineSurrogates (hi lo : Nat) : Nat :=
  0x10000 + (hi - 0xD800) * 0x400 + (lo - 0xDC00)

/--
The contents of a string, starting just after the opening quotation mark.

An unpaired surrogate escape is an error rather than a replacement character, so text that cannot
be represented is never silently altered.
-/
def string (input : List Char) (pos : Nat) (acc : String) :
    Except Error (Scanned String input) :=
  match input with
  | [] => .error ⟨pos, .unexpectedEnd⟩
  | '"' :: rest => .ok ⟨acc, rest, pos + 1, by simp⟩
  | '\\' :: 'u' :: c₁ :: c₂ :: c₃ :: c₄ :: afterHex =>
    match hex4? c₁ c₂ c₃ c₄ with
    | none => .error ⟨pos + 2, .badHexEscape⟩
    | some v =>
      if v < 0xD800 || 0xDFFF < v then
        match charOfCodePoint? v with
        | none => .error ⟨pos + 2, .badHexEscape⟩
        | some c =>
          match string afterHex (pos + 6) (acc.push c) with
          | .error e => .error e
          | .ok r => .ok ⟨r.value, r.rest, r.pos, by have := r.consumed; simp; omega⟩
      else if v ≤ 0xDBFF then
        match afterHex with
        | '\\' :: 'u' :: d₁ :: d₂ :: d₃ :: d₄ :: afterLow =>
          match hex4? d₁ d₂ d₃ d₄ with
          | none => .error ⟨pos + 8, .badHexEscape⟩
          | some lo =>
            if 0xDC00 ≤ lo && lo ≤ 0xDFFF then
              match charOfCodePoint? (combineSurrogates v lo) with
              | none => .error ⟨pos + 2, .badHexEscape⟩
              | some c =>
                match string afterLow (pos + 12) (acc.push c) with
                | .error e => .error e
                | .ok r => .ok ⟨r.value, r.rest, r.pos, by have := r.consumed; simp; omega⟩
            else
              .error ⟨pos + 2, .loneSurrogate⟩
        | _ => .error ⟨pos + 2, .loneSurrogate⟩
      else
        .error ⟨pos + 2, .loneSurrogate⟩
  | '\\' :: c :: afterEscape =>
    match escapeChar? c with
    | none => .error ⟨pos + 1, .unknownEscape c⟩
    | some ch =>
      match string afterEscape (pos + 2) (acc.push ch) with
      | .error e => .error e
      | .ok r => .ok ⟨r.value, r.rest, r.pos, by have := r.consumed; simp; omega⟩
  | '\\' :: [] => .error ⟨pos + 1, .unexpectedEnd⟩
  | c :: rest =>
    if Spec.isUnescaped c then
      match string rest (pos + 1) (acc.push c) with
      | .error e => .error e
      | .ok r => .ok ⟨r.value, r.rest, r.pos, by have := r.consumed; simp; omega⟩
    else
      .error ⟨pos, .controlCharInString c⟩

/-! ## Numbers -/

/-- `*DIGIT`, accumulating the most significant digit first. -/
def digits (input : List Char) (pos value count : Nat) : Consumed (Nat × Nat) input :=
  match input with
  | c :: rest =>
    if Spec.isDigit c then
      let r := digits rest (pos + 1) (value * 10 + Spec.digitVal c) (count + 1)
      ⟨r.value, r.rest, r.pos, by have := r.notLonger; simp; omega⟩
    else
      ⟨(value, count), c :: rest, pos, by simp⟩
  | [] => ⟨(value, count), [], pos, by simp⟩

/-- `int = zero / ( digit1-9 *DIGIT )`. A leading zero stands alone, so `01` is two tokens. -/
def intPart (input : List Char) (pos : Nat) : Except Error (Scanned (Nat × Nat) input) :=
  match input with
  | '0' :: rest => .ok ⟨(0, 1), rest, pos + 1, by simp⟩
  | c :: rest =>
    if Spec.isDigit c then
      let r := digits rest (pos + 1) (Spec.digitVal c) 1
      .ok ⟨r.value, r.rest, r.pos, by have := r.notLonger; simp; omega⟩
    else
      .error ⟨pos, .expectedDigit⟩
  | [] => .error ⟨pos, .expectedDigit⟩

/-- `frac = decimal-point 1*DIGIT`, optional. -/
def fracPart (input : List Char) (pos : Nat) : Except Error (Consumed (Nat × Nat) input) :=
  match input with
  | '.' :: c :: rest =>
    if Spec.isDigit c then
      let r := digits rest (pos + 2) (Spec.digitVal c) 1
      .ok ⟨r.value, r.rest, r.pos, by have := r.notLonger; simp; omega⟩
    else
      .error ⟨pos + 1, .expectedDigit⟩
  | '.' :: [] => .error ⟨pos + 1, .expectedDigit⟩
  | other => .ok ⟨(0, 0), other, pos, Nat.le_refl _⟩

/-- `exp = e [ minus / plus ] 1*DIGIT`, optional. -/
def expPart (input : List Char) (pos : Nat) : Except Error (Consumed (Int × Nat) input) :=
  match input with
  | e :: '+' :: c :: rest =>
    if e == 'e' || e == 'E' then
      if Spec.isDigit c then
        let r := digits rest (pos + 3) (Spec.digitVal c) 1
        .ok ⟨((r.value.1 : Int), r.value.2), r.rest, r.pos, by
          have := r.notLonger; simp; omega⟩
      else
        .error ⟨pos + 2, .expectedDigit⟩
    else
      .ok ⟨(0, 0), e :: '+' :: c :: rest, pos, Nat.le_refl _⟩
  | e :: '-' :: c :: rest =>
    if e == 'e' || e == 'E' then
      if Spec.isDigit c then
        let r := digits rest (pos + 3) (Spec.digitVal c) 1
        .ok ⟨(-(r.value.1 : Int), r.value.2), r.rest, r.pos, by
          have := r.notLonger; simp; omega⟩
      else
        .error ⟨pos + 2, .expectedDigit⟩
    else
      .ok ⟨(0, 0), e :: '-' :: c :: rest, pos, Nat.le_refl _⟩
  | e :: c :: rest =>
    if e == 'e' || e == 'E' then
      if Spec.isDigit c then
        let r := digits rest (pos + 2) (Spec.digitVal c) 1
        .ok ⟨((r.value.1 : Int), r.value.2), r.rest, r.pos, by
          have := r.notLonger; simp; omega⟩
      else
        .error ⟨pos + 1, .expectedDigit⟩
    else
      .ok ⟨(0, 0), e :: c :: rest, pos, Nat.le_refl _⟩
  | e :: [] =>
    if e == 'e' || e == 'E' then .error ⟨pos + 1, .expectedDigit⟩
    else .ok ⟨(0, 0), [e], pos, Nat.le_refl _⟩
  | [] => .ok ⟨(0, 0), [], pos, Nat.le_refl _⟩

def tooManyDigits (cfg : Config) (n : Nat) : Bool :=
  match cfg.maxNumberDigits with
  | some limit => limit < n
  | none => false

/--
`number = [ minus ] int [ frac ] [ exp ]`.

The exponent is recorded, never applied, so `1e1000000000` costs no more than a short number.
What is bounded is the count of digits, because a mantissa is built from them one at a time.
-/
def unsignedNumber (cfg : Config) (input : List Char) (pos : Nat) (neg : Bool) :
    Except Error (Scanned Number input) :=
  match intPart input pos with
  | .error e => .error e
  | .ok i =>
    match fracPart i.rest i.pos with
    | .error e => .error e
    | .ok f =>
      match expPart f.rest f.pos with
      | .error e => .error e
      | .ok x =>
        if tooManyDigits cfg (i.value.2 + f.value.2) || tooManyDigits cfg x.value.2 then
          .error ⟨pos, .tooManyDigits⟩
        else
          let magnitude : Nat := i.value.1 * 10 ^ f.value.2 + f.value.1
          let mantissa : Int := if neg then -(magnitude : Int) else (magnitude : Int)
          .ok ⟨Number.normalize mantissa (x.value.1 - (f.value.2 : Int)), x.rest, x.pos, by
            have := i.consumed
            have := f.notLonger
            have := x.notLonger
            omega⟩

def number (cfg : Config) (input : List Char) (pos : Nat) : Except Error (Scanned Number input) :=
  match input with
  | '-' :: rest =>
    match unsignedNumber cfg rest (pos + 1) true with
    | .error e => .error e
    | .ok r => .ok ⟨r.value, r.rest, r.pos, by have := r.consumed; simp; omega⟩
  | c :: rest => unsignedNumber cfg (c :: rest) pos false
  | [] => .error ⟨pos, .unexpectedEnd⟩

/-! ## The machine -/

/--
What remains to be filled in once the value being read is complete. Holding these on the heap is
what keeps nesting off the C stack, so depth costs memory rather than risking a crash.
-/
inductive Frame where
  | arr (elems : Array Json)
  | obj (fields : Array (String × Json)) (seen : Std.HashSet String) (name : String)

def depthExceeded (cfg : Config) (depth : Nat) : Bool :=
  match cfg.maxDepth with
  | some limit => limit ≤ depth
  | none => false

mutual

/-- Read one value, then hand it to the enclosing frames. -/
def value (cfg : Config) (input : List Char) (pos depth : Nat) (stack : List Frame) :
    Except Error (Json × List Char × Nat) :=
  match input with
  | 'n' :: 'u' :: 'l' :: 'l' :: rest => continueWith cfg .null rest (pos + 4) depth stack
  | 't' :: 'r' :: 'u' :: 'e' :: rest => continueWith cfg (.bool true) rest (pos + 4) depth stack
  | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: rest =>
    continueWith cfg (.bool false) rest (pos + 5) depth stack
  | '"' :: rest =>
    match string rest (pos + 1) "" with
    | .error e => .error e
    | .ok ⟨s, srest, spos, _⟩ => continueWith cfg (.str s) srest spos depth stack
  | '[' :: rest =>
    if depthExceeded cfg depth then .error ⟨pos, .depthExceeded⟩
    else
      match skipWs rest (pos + 1) with
      | ⟨_, wrest, wpos, _⟩ =>
        match hw : wrest with
        | ']' :: after => continueWith cfg (.arr #[]) after (wpos + 1) depth stack
        | other => value cfg other wpos (depth + 1) (.arr #[] :: stack)
  | '{' :: rest =>
    if depthExceeded cfg depth then .error ⟨pos, .depthExceeded⟩
    else
      match skipWs rest (pos + 1) with
      | ⟨_, wrest, wpos, _⟩ =>
        match hw : wrest with
        | '}' :: after => continueWith cfg (.obj #[]) after (wpos + 1) depth stack
        | other => member cfg other wpos (depth + 1) #[] ∅ stack
  | c :: rest =>
    if c == '-' || Spec.isDigit c then
      match number cfg (c :: rest) pos with
      | .error e => .error e
      | .ok ⟨n, nrest, npos, _⟩ => continueWith cfg (.num n) nrest npos depth stack
    else
      .error ⟨pos, .unexpectedChar c⟩
  | [] => .error ⟨pos, .unexpectedEnd⟩
termination_by input.length
decreasing_by all_goals first | omega | (simp_all; omega) | simp_all

/-- A value has just been completed; give it to the innermost frame. -/
def continueWith (cfg : Config) (v : Json) (input : List Char) (pos depth : Nat)
    (stack : List Frame) : Except Error (Json × List Char × Nat) :=
  match stack with
  | [] => .ok (v, input, pos)
  | .arr elems :: outer =>
    match skipWs input pos with
    | ⟨_, wrest, wpos, _⟩ =>
      match hw : wrest with
      | ',' :: after =>
        match skipWs after (wpos + 1) with
        | ⟨_, w₂rest, w₂pos, _⟩ =>
          value cfg w₂rest w₂pos depth (.arr (elems.push v) :: outer)
      | ']' :: after => continueWith cfg (.arr (elems.push v)) after (wpos + 1) (depth - 1) outer
      | c :: _ => .error ⟨wpos, .unexpectedChar c⟩
      | [] => .error ⟨wpos, .unexpectedEnd⟩
  | .obj fields seen name :: outer =>
    match skipWs input pos with
    | ⟨_, wrest, wpos, _⟩ =>
      match hw : wrest with
      | ',' :: after =>
        match skipWs after (wpos + 1) with
        | ⟨_, w₂rest, w₂pos, _⟩ =>
          member cfg w₂rest w₂pos depth (fields.push (name, v)) seen outer
      | '}' :: after =>
        continueWith cfg (.obj (fields.push (name, v))) after (wpos + 1) (depth - 1) outer
      | c :: _ => .error ⟨wpos, .unexpectedChar c⟩
      | [] => .error ⟨wpos, .unexpectedEnd⟩
termination_by input.length
decreasing_by all_goals first | omega | (simp_all; omega) | simp_all

/-- Having just seen `{` or `,` inside an object, read a member's name and its colon. -/
def member (cfg : Config) (input : List Char) (pos depth : Nat)
    (fields : Array (String × Json)) (seen : Std.HashSet String) (stack : List Frame) :
    Except Error (Json × List Char × Nat) :=
  match input with
  | '"' :: rest =>
    match string rest (pos + 1) "" with
    | .error e => .error e
    | .ok ⟨k, krest, kpos, _⟩ =>
      if cfg.duplicateKeys == .reject && seen.contains k then
        .error ⟨pos, .duplicateKey k⟩
      else
        match skipWs krest kpos with
        | ⟨_, wrest, wpos, _⟩ =>
          match _hw : wrest with
          | ':' :: after =>
            match skipWs after (wpos + 1) with
            | ⟨_, w₂rest, w₂pos, _⟩ =>
              value cfg w₂rest w₂pos depth (.obj fields (seen.insert k) k :: stack)
          | c :: _ => .error ⟨wpos, .unexpectedChar c⟩
          | [] => .error ⟨wpos, .unexpectedEnd⟩
  | c :: _ => .error ⟨pos, .unexpectedChar c⟩
  | [] => .error ⟨pos, .unexpectedEnd⟩
termination_by input.length
decreasing_by all_goals first | omega | (simp_all; omega) | simp_all

end

/-! ## Entry points -/

/-- Parse JSON text. Text that is not a single complete value is an error, never a partial value. -/
def parse (s : String) (cfg : Config := {}) : Except Error Json :=
  let chars := s.toList
  let chars :=
    match chars with
    | c :: rest => if cfg.ignoreBOM && c.toNat == 0xFEFF then rest else chars
    | [] => chars
  let w := skipWs chars 0
  match value cfg w.rest w.pos 0 [] with
  | .error e => .error e
  | .ok (j, rest, pos) =>
    let w₂ := skipWs rest pos
    match w₂.rest with
    | [] => .ok j
    | c :: _ => .error ⟨w₂.pos, .trailingText c⟩

/--
Parse JSON text from bytes. RFC 8259 section 8.1 requires UTF-8, and that is enforced here by the
verified decoder in `Init.Data.String.Decode`.
-/
def parseBytes (b : ByteArray) (cfg : Config := {}) : Except Error Json :=
  match String.fromUTF8? b with
  | some s => parse s cfg
  | none => .error ⟨0, .invalidUtf8⟩

end Parser

@[inherit_doc Parser.parse]
def parse (s : String) (cfg : Config := {}) : Except Error Json := Parser.parse s cfg

@[inherit_doc Parser.parseBytes]
def parseBytes (b : ByteArray) (cfg : Config := {}) : Except Error Json := Parser.parseBytes b cfg

end Json
