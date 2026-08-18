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

/-- A failure, with the byte offset into the text at which it was detected. -/
structure Error where
  byteOffset : Nat
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

instance : ToString Error := ⟨fun e => s!"{e.kind.describe} at byte {e.byteOffset}"⟩


namespace Parser

/-!
The scanner walks the text by position rather than converting it to a list of characters first.
That conversion cost about thirty bytes for every byte of input, which put a limit on the size of
document that could safely be read; a position costs nothing, so what a parse holds is the text
and the value.
-/

section
variable {s : String}

/-- Where a position is, as a byte offset, which is what an error reports. -/
def byteOffset (p : s.Pos) : Nat := p.offset.byteIdx

/-- The character at `p` and the position after it, or nothing at the end of the text. -/
@[inline]
def step? (p : s.Pos) : Option (Char × s.Pos) :=
  if h : p = s.endPos then none else some (p.get h, p.next h)

theorem step?_lt {p q : s.Pos} {c : Char} (h : step? p = some (c, q)) :
    q.remainingBytes < p.remainingBytes := by
  rw [step?] at h
  split at h
  · simp at h
  · rw [Option.some.injEq, Prod.mk.injEq] at h
    exact (String.Pos.lt_iff_remainingBytes_lt _ _).mp (h.2 ▸ String.Pos.lt_next)

/--
A scan that consumed at least one character. Carrying the proof here rather than proving it
afterwards keeps the machine's termination argument to one line per call.
-/
structure Scanned (α : Type) (start : s.Pos) where
  value : α
  pos : s.Pos
  consumed : pos.remainingBytes < start.remainingBytes

/-- A scan that may have consumed nothing, as whitespace and the optional productions can. -/
structure Consumed (α : Type) (start : s.Pos) where
  value : α
  pos : s.Pos
  notLonger : pos.remainingBytes ≤ start.remainingBytes

/-! ## Leaf scanners -/

/--
Whitespace, if there is any.

Written as a loop over a position that carries how far it has come, rather than as a recursion
whose result is rebuilt on the way out, so that a long run costs no stack and holds nothing per
character.
-/
def skipWs (start : s.Pos) : Consumed Unit start := go start (Nat.le_refl _)
where
  go (p : s.Pos) (h : p.remainingBytes ≤ start.remainingBytes) : Consumed Unit start :=
    match hc : step? p with
    | some (c, q) =>
      if Spec.isWs c then go q (by have := step?_lt hc; omega)
      else ⟨(), p, h⟩
    | none => ⟨(), p, h⟩
  termination_by p.remainingBytes
  decreasing_by exact step?_lt hc

/-- The characters of `l` in order, if the text at `p` begins with them. -/
def expect? (p : s.Pos) : List Char → Option (Consumed Unit p)
  | [] => some ⟨(), p, Nat.le_refl _⟩
  | c :: rest =>
    match hc : step? p with
    | some (c', q) =>
      if c == c' then
        match expect? q rest with
        | some r => some ⟨(), r.pos, by have := r.notLonger; have := step?_lt hc; omega⟩
        | none => none
      else none
    | none => none

/-- One hexadecimal digit, as a number. -/
def hexDigit? (p : s.Pos) : Option (Scanned Nat p) :=
  match hc : step? p with
  | some (c, q) =>
    match Spec.hexVal? c with
    | some v => some ⟨v, q, step?_lt hc⟩
    | none => none
  | none => none

/-- `4HEXDIG`, the body of a `\u` escape. -/
def hex4? (p : s.Pos) : Option (Scanned Nat p) :=
  match hexDigit? p with
  | none => none
  | some r₁ =>
    match hexDigit? r₁.pos with
    | none => none
    | some r₂ =>
      match hexDigit? r₂.pos with
      | none => none
      | some r₃ =>
        match hexDigit? r₃.pos with
        | none => none
        | some r₄ =>
          some ⟨r₁.value * 4096 + r₂.value * 256 + r₃.value * 16 + r₄.value, r₄.pos, by
            have := r₁.consumed; have := r₂.consumed; have := r₃.consumed; have := r₄.consumed
            omega⟩

/-- A whole `\uXXXX` escape, which is how the low half of a surrogate pair is looked for. -/
def escapeHex4? (p : s.Pos) : Option (Scanned Nat p) :=
  match hc : step? p with
  | some ('\\', q) =>
    match hu : step? q with
    | some ('u', r) =>
      match hex4? r with
      | some h =>
        some ⟨h.value, h.pos, by
          have := h.consumed; have := step?_lt hc; have := step?_lt hu; omega⟩
      | none => none
    | _ => none
  | _ => none

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
What the next piece of a string is: its end, one character of it, or a failure. Reading a piece
and recursing once keeps `string` to a single recursive call, and so to a one-line termination
argument, where the escapes would otherwise each need their own.
-/
inductive StringStep {s : String} (p : s.Pos) where
  | done (pos : s.Pos) (consumed : pos.remainingBytes < p.remainingBytes)
  | char (c : Char) (pos : s.Pos) (consumed : pos.remainingBytes < p.remainingBytes)
  | fail (e : Error)

/--
One piece of a string, starting at `p`, which is either just after the opening quotation mark or
just after the last piece.

An unpaired surrogate escape is an error rather than a replacement character, so text that cannot
be represented is never silently altered.
-/
def stringStep (p : s.Pos) : StringStep p :=
  match hc : step? p with
  | none => .fail ⟨byteOffset p, .unexpectedEnd⟩
  | some ('"', q) => .done q (step?_lt hc)
  | some ('\\', q) =>
    match hu : step? q with
    | none => .fail ⟨byteOffset q, .unexpectedEnd⟩
    | some ('u', r) =>
      match hex4? r with
      | none => .fail ⟨byteOffset r, .badHexEscape⟩
      | some h =>
        if h.value < 0xD800 || 0xDFFF < h.value then
          match charOfCodePoint? h.value with
          | none => .fail ⟨byteOffset r, .badHexEscape⟩
          | some c =>
            .char c h.pos (by
              have := h.consumed; have := step?_lt hc; have := step?_lt hu; omega)
        else if h.value ≤ 0xDBFF then
          match escapeHex4? h.pos with
          | none => .fail ⟨byteOffset r, .loneSurrogate⟩
          | some lo =>
            if 0xDC00 ≤ lo.value && lo.value ≤ 0xDFFF then
              match charOfCodePoint? (combineSurrogates h.value lo.value) with
              | none => .fail ⟨byteOffset r, .badHexEscape⟩
              | some c =>
                .char c lo.pos (by
                  have := lo.consumed; have := h.consumed
                  have := step?_lt hc; have := step?_lt hu; omega)
            else
              .fail ⟨byteOffset r, .loneSurrogate⟩
        else
          .fail ⟨byteOffset r, .loneSurrogate⟩
    | some (c, r) =>
      match escapeChar? c with
      | none => .fail ⟨byteOffset q, .unknownEscape c⟩
      | some ch => .char ch r (by have := step?_lt hc; have := step?_lt hu; omega)
  | some (c, q) =>
    if Spec.isUnescaped c then .char c q (step?_lt hc)
    else .fail ⟨byteOffset p, .controlCharInString c⟩

/--
The contents of a string, starting just after the opening quotation mark.

A loop rather than a recursion that rebuilds its result on the way out: a string of a million
characters would otherwise hold a frame and a step apiece until the closing quotation mark.
-/
def string (start : s.Pos) (acc : String) : Except Error (Scanned String start) :=
  go start acc (Nat.le_refl _)
where
  go (p : s.Pos) (acc : String) (h : p.remainingBytes ≤ start.remainingBytes) :
      Except Error (Scanned String start) :=
    match hs : stringStep p with
    | .fail e => .error e
    | .done q hq => .ok ⟨acc, q, by omega⟩
    | .char c q hq => go q (acc.push c) (by omega)
  termination_by p.remainingBytes
  decreasing_by exact hq

/-! ## Numbers -/

/-- `*DIGIT`, accumulating the most significant digit first, and as a loop for the same reason. -/
def digits (start : s.Pos) (value count : Nat) : Consumed (Nat × Nat) start :=
  go start value count (Nat.le_refl _)
where
  go (p : s.Pos) (value count : Nat) (h : p.remainingBytes ≤ start.remainingBytes) :
      Consumed (Nat × Nat) start :=
    match hc : step? p with
    | some (c, q) =>
      if Spec.isDigit c then
        go q (value * 10 + Spec.digitVal c) (count + 1) (by have := step?_lt hc; omega)
      else
        ⟨(value, count), p, h⟩
    | none => ⟨(value, count), p, h⟩
  termination_by p.remainingBytes
  decreasing_by exact step?_lt hc

/-- `int = zero / ( digit1-9 *DIGIT )`. A leading zero stands alone, so `01` is two tokens. -/
def intPart (p : s.Pos) : Except Error (Scanned (Nat × Nat) p) :=
  match hc : step? p with
  | some ('0', q) => .ok ⟨(0, 1), q, step?_lt hc⟩
  | some (c, q) =>
    if Spec.isDigit c then
      let r := digits q (Spec.digitVal c) 1
      .ok ⟨r.value, r.pos, by have := r.notLonger; have := step?_lt hc; omega⟩
    else
      .error ⟨byteOffset p, .expectedDigit⟩
  | none => .error ⟨byteOffset p, .expectedDigit⟩

/-- `frac = decimal-point 1*DIGIT`, optional. -/
def fracPart (p : s.Pos) : Except Error (Consumed (Nat × Nat) p) :=
  match hc : step? p with
  | some ('.', q) =>
    match hd : step? q with
    | some (c, r) =>
      if Spec.isDigit c then
        let t := digits r (Spec.digitVal c) 1
        .ok ⟨t.value, t.pos, by
          have := t.notLonger; have := step?_lt hc; have := step?_lt hd; omega⟩
      else
        .error ⟨byteOffset q, .expectedDigit⟩
    | none => .error ⟨byteOffset q, .expectedDigit⟩
  | _ => .ok ⟨(0, 0), p, Nat.le_refl _⟩

/-- An optional `+` or `-`, reporting whether it was a minus. -/
def expSign (p : s.Pos) : Consumed Bool p :=
  match hs : step? p with
  | some ('+', q) => ⟨false, q, Nat.le_of_lt (step?_lt hs)⟩
  | some ('-', q) => ⟨true, q, Nat.le_of_lt (step?_lt hs)⟩
  | _ => ⟨false, p, Nat.le_refl _⟩

/-- `exp = e [ minus / plus ] 1*DIGIT`, optional. -/
def expPart (p : s.Pos) : Except Error (Consumed (Int × Nat) p) :=
  match he : step? p with
  | some (e, q) =>
    if e == 'e' || e == 'E' then
      match expSign q with
      | ⟨negative, r, hsign⟩ =>
        match hd : step? r with
        | some (c, t) =>
          if Spec.isDigit c then
            let u := digits t (Spec.digitVal c) 1
            .ok ⟨(if negative then -(u.value.1 : Int) else (u.value.1 : Int), u.value.2), u.pos, by
              have := u.notLonger; have := step?_lt he; have := step?_lt hd; omega⟩
          else
            .error ⟨byteOffset r, .expectedDigit⟩
        | none => .error ⟨byteOffset r, .expectedDigit⟩
    else
      .ok ⟨(0, 0), p, Nat.le_refl _⟩
  | none => .ok ⟨(0, 0), p, Nat.le_refl _⟩

def tooManyDigits (cfg : Config) (n : Nat) : Bool :=
  match cfg.maxNumberDigits with
  | some limit => limit < n
  | none => false

/--
`number = [ minus ] int [ frac ] [ exp ]`.

The exponent is recorded, never applied, so `1e1000000000` costs no more than a short number.
What is bounded is the count of digits, because a mantissa is built from them one at a time.
-/
def unsignedNumber (cfg : Config) (p : s.Pos) (neg : Bool) : Except Error (Scanned Number p) :=
  match intPart p with
  | .error e => .error e
  | .ok i =>
    match fracPart i.pos with
    | .error e => .error e
    | .ok f =>
      match expPart f.pos with
      | .error e => .error e
      | .ok x =>
        if tooManyDigits cfg (i.value.2 + f.value.2) || tooManyDigits cfg x.value.2 then
          .error ⟨byteOffset p, .tooManyDigits⟩
        else
          let magnitude : Nat := i.value.1 * 10 ^ f.value.2 + f.value.1
          let mantissa : Int := if neg then -(magnitude : Int) else (magnitude : Int)
          .ok ⟨Number.normalize mantissa (x.value.1 - (f.value.2 : Int)), x.pos, by
            have := i.consumed
            have := f.notLonger
            have := x.notLonger
            omega⟩

def number (cfg : Config) (p : s.Pos) : Except Error (Scanned Number p) :=
  match hc : step? p with
  | some ('-', q) =>
    match unsignedNumber cfg q true with
    | .error e => .error e
    | .ok r => .ok ⟨r.value, r.pos, by have := r.consumed; have := step?_lt hc; omega⟩
  | some _ => unsignedNumber cfg p false
  | none => .error ⟨byteOffset p, .unexpectedEnd⟩

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
def value (cfg : Config) (p : s.Pos) (depth : Nat) (stack : List Frame) :
    Except Error (Json × s.Pos) :=
  match _hc : step? p with
  | none => .error ⟨byteOffset p, .unexpectedEnd⟩
  | some ('n', q) =>
    match expect? q ['u', 'l', 'l'] with
    | some ⟨_, r, _hr⟩ => continueWith cfg .null r depth stack
    | none => .error ⟨byteOffset p, .unexpectedChar 'n'⟩
  | some ('t', q) =>
    match expect? q ['r', 'u', 'e'] with
    | some ⟨_, r, _hr⟩ => continueWith cfg (.bool true) r depth stack
    | none => .error ⟨byteOffset p, .unexpectedChar 't'⟩
  | some ('f', q) =>
    match expect? q ['a', 'l', 's', 'e'] with
    | some ⟨_, r, _hr⟩ => continueWith cfg (.bool false) r depth stack
    | none => .error ⟨byteOffset p, .unexpectedChar 'f'⟩
  | some ('"', q) =>
    match string q "" with
    | .error e => .error e
    | .ok ⟨text, r, _hr⟩ => continueWith cfg (.str text) r depth stack
  | some ('[', q) =>
    if depthExceeded cfg depth then .error ⟨byteOffset p, .depthExceeded⟩
    else
      match skipWs q with
      | ⟨_, w, _hw⟩ =>
        match _hb : step? w with
        | some (']', after) => continueWith cfg (.arr #[]) after depth stack
        | _ => value cfg w (depth + 1) (.arr #[] :: stack)
  | some ('{', q) =>
    if depthExceeded cfg depth then .error ⟨byteOffset p, .depthExceeded⟩
    else
      match skipWs q with
      | ⟨_, w, _hw⟩ =>
        match _hb : step? w with
        | some ('}', after) => continueWith cfg (.obj #[]) after depth stack
        | _ => member cfg w (depth + 1) #[] ∅ stack
  | some (c, _) =>
    if c == '-' || Spec.isDigit c then
      match number cfg p with
      | .error e => .error e
      | .ok ⟨n, r, _hr⟩ => continueWith cfg (.num n) r depth stack
    else
      .error ⟨byteOffset p, .unexpectedChar c⟩
termination_by p.remainingBytes
decreasing_by
  all_goals
    first
      | omega
      | (have := step?_lt _hc; omega)
      | (have := step?_lt _hc; have := step?_lt _hb; omega)

/-- A value has just been completed; give it to the innermost frame. -/
def continueWith (cfg : Config) (v : Json) (p : s.Pos) (depth : Nat) (stack : List Frame) :
    Except Error (Json × s.Pos) :=
  match stack with
  | [] => .ok (v, p)
  | .arr elems :: outer =>
    match skipWs p with
    | ⟨_, w, _hw⟩ =>
      match _hb : step? w with
      | some (',', after) =>
        match skipWs after with
        | ⟨_, w₂, _hw₂⟩ => value cfg w₂ depth (.arr (elems.push v) :: outer)
      | some (']', after) => continueWith cfg (.arr (elems.push v)) after (depth - 1) outer
      | some (c, _) => .error ⟨byteOffset w, .unexpectedChar c⟩
      | none => .error ⟨byteOffset w, .unexpectedEnd⟩
  | .obj fields seen name :: outer =>
    match skipWs p with
    | ⟨_, w, _hw⟩ =>
      match _hb : step? w with
      | some (',', after) =>
        match skipWs after with
        | ⟨_, w₂, _hw₂⟩ => member cfg w₂ depth (fields.push (name, v)) seen outer
      | some ('}', after) =>
        continueWith cfg (.obj (fields.push (name, v))) after (depth - 1) outer
      | some (c, _) => .error ⟨byteOffset w, .unexpectedChar c⟩
      | none => .error ⟨byteOffset w, .unexpectedEnd⟩
termination_by p.remainingBytes
decreasing_by all_goals (have := step?_lt _hb; omega)

/-- Having just seen `{` or `,` inside an object, read a member's name and its colon. -/
def member (cfg : Config) (p : s.Pos) (depth : Nat) (fields : Array (String × Json))
    (seen : Std.HashSet String) (stack : List Frame) : Except Error (Json × s.Pos) :=
  match _hc : step? p with
  | some ('"', q) =>
    match string q "" with
    | .error e => .error e
    | .ok ⟨name, k, _hk⟩ =>
      if cfg.duplicateKeys == .reject && seen.contains name then
        .error ⟨byteOffset p, .duplicateKey name⟩
      else
        match skipWs k with
        | ⟨_, w, _hw⟩ =>
          match _hb : step? w with
          | some (':', after) =>
            match skipWs after with
            | ⟨_, w₂, _hw₂⟩ => value cfg w₂ depth (.obj fields (seen.insert name) name :: stack)
          | some (c, _) => .error ⟨byteOffset w, .unexpectedChar c⟩
          | none => .error ⟨byteOffset w, .unexpectedEnd⟩
  | some (c, _) => .error ⟨byteOffset p, .unexpectedChar c⟩
  | none => .error ⟨byteOffset p, .unexpectedEnd⟩
termination_by p.remainingBytes
decreasing_by all_goals (have := step?_lt _hc; have := step?_lt _hb; omega)

end

end

/-! ## Entry points -/

/-- Parse JSON text. Text that is not a single complete value is an error, never a partial value. -/
def parse (s : String) (cfg : Config := {}) : Except Error Json :=
  let start :=
    match step? s.startPos with
    | some (c, q) => if cfg.ignoreBOM && c.toNat == 0xFEFF then q else s.startPos
    | none => s.startPos
  let w := skipWs start
  match value cfg w.pos 0 [] with
  | .error e => .error e
  | .ok (j, p) =>
    let w₂ := skipWs p
    match step? w₂.pos with
    | none => .ok j
    | some (c, _) => .error ⟨byteOffset w₂.pos, .trailingText c⟩

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
