/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Json.Basic

public section

namespace Json.Printer

@[expose] section

/-!
Writing a value out as text.

`compress` and `pretty` share one traversal over an explicit stack of items, so nesting costs
heap rather than C stack, and the text accumulates in a `String`, which makes the validity of
its UTF-8 a property of the type rather than something to maintain by hand.

A number is written out in full while its padding stays short and in exponent notation
otherwise, so `⟨1,2⟩` is `100` and `⟨1,1000000000⟩` is `1e1000000000`. Both read back as the
number they came from.
-/

/-! ## Digits -/

def digitChar (d : Nat) : Char := Char.ofNat ('0'.toNat + d)

def hexDigitChar (d : Nat) : Char :=
  if d < 10 then digitChar d else Char.ofNat ('a'.toNat + (d - 10))

/-- The decimal digits of `n` in front of `acc`, most significant first. -/
def digitCharsTo (n : Nat) (acc : List Char) : List Char :=
  if n < 10 then digitChar n :: acc
  else digitCharsTo (n / 10) (digitChar (n % 10) :: acc)
termination_by n
decreasing_by omega

def digitChars (n : Nat) : List Char := digitCharsTo n []

def digitString (n : Nat) : String := String.ofList (digitChars n)

def zeros (n : Nat) : String := String.ofList (List.replicate n '0')

def spaces (n : Nat) : String := String.ofList (List.replicate n ' ')

/-! ## Numbers -/

/-- Padding longer than this is written as an exponent instead. -/
def plainZeroLimit : Nat := 20

/--
A number as JSON text: plain decimal notation while that costs at most `plainZeroLimit`
characters of padding, and exponent notation beyond it, so `⟨1, 2⟩` is `100` while
`⟨1, 1000000000⟩` is `1e1000000000`. Both spellings denote the same value, so round tripping
is unaffected by which one is chosen.
-/
def number (n : Number) : String :=
  if n.mantissa = 0 then
    "0"
  else
    let sign := if n.mantissa < 0 then "-" else ""
    let ds := digitChars n.mantissa.natAbs
    let mantissa := String.ofList ds
    let exponentForm :=
      if n.exponent < 0 then mantissa ++ "e-" ++ digitString (-n.exponent).toNat
      else mantissa ++ "e" ++ digitString n.exponent.toNat
    if n.exponent = 0 then
      sign ++ mantissa
    else if 0 < n.exponent then
      if n.exponent ≤ (plainZeroLimit : Int) then sign ++ mantissa ++ zeros n.exponent.toNat
      else sign ++ exponentForm
    else
      let k := (-n.exponent).toNat
      if k < ds.length then
        sign ++ String.ofList (ds.take (ds.length - k)) ++ "." ++
          String.ofList (ds.drop (ds.length - k))
      else if k - ds.length ≤ plainZeroLimit then
        sign ++ "0." ++ zeros (k - ds.length) ++ mantissa
      else
        sign ++ exponentForm

/-! ## Strings -/

/--
`c` as it appears inside a string literal: the two escapes RFC 8259 requires, the short forms
for the control characters that have one, and `\uXXXX` for the remaining controls. Everything
else stands for itself, the output being UTF-8.
-/
def escapeChars (c : Char) : List Char :=
  match c with
  | '"' => ['\\', '"']
  | '\\' => ['\\', '\\']
  | '\x08' => ['\\', 'b']
  | '\x0c' => ['\\', 'f']
  | '\n' => ['\\', 'n']
  | '\x0d' => ['\\', 'r']
  | '\t' => ['\\', 't']
  | c =>
    if c.toNat < 0x20 then
      ['\\', 'u', '0', '0', hexDigitChar (c.toNat / 16), hexDigitChar (c.toNat % 16)]
    else
      [c]

def escapeCharTo (acc : String) (c : Char) : String :=
  match c with
  | '"' => acc ++ "\\\""
  | '\\' => acc ++ "\\\\"
  | '\x08' => acc ++ "\\b"
  | '\x0c' => acc ++ "\\f"
  | '\n' => acc ++ "\\n"
  | '\x0d' => acc ++ "\\r"
  | '\t' => acc ++ "\\t"
  | c =>
    if c.toNat < 0x20 then
      ((acc ++ "\\u00").push (hexDigitChar (c.toNat / 16))).push (hexDigitChar (c.toNat % 16))
    else
      acc.push c

def escapeTo (acc : String) (s : String) : String := s.foldl escapeCharTo acc

/-- `s` as a string literal, quotation marks included, appended to `acc`. -/
def stringTo (acc : String) (s : String) : String := (escapeTo (acc.push '"') s).push '"'

def string (s : String) : String := stringTo "" s

/-! ## Layout -/

/-- How a value is laid out: `none` for the compact form, `some k` to indent each level by `k`. -/
structure Style where
  indent : Option Nat
deriving Inhabited

def Style.compact : Style := ⟨none⟩

def Style.pretty (indent : Nat := 2) : Style := ⟨some indent⟩

/-- The break and indentation that precede an item at `depth`, empty in the compact form. -/
def Style.lineBreak (st : Style) (depth : Nat) : String :=
  match st.indent with
  | none => ""
  | some k => "\n" ++ spaces (k * depth)

def Style.colon (st : Style) : String :=
  match st.indent with
  | none => ":"
  | some _ => ": "

/-! ## The traversal -/

/--
One step of pending output: text already decided, a value still to render, or the elements or
members of a container that has been entered. `first` distinguishes the item that follows the
opening bracket from those that need a separator in front of them.
-/
inductive Item where
  | lit (s : String)
  | val (depth : Nat) (j : Json)
  | elems (depth : Nat) (rest : List Json) (first : Bool)
  | members (depth : Nat) (rest : List (String × Json)) (first : Bool)

-- The measure the traversal decreases. Only the shape counts: each element or member allows for
-- the separator that may precede it, and each container for its two brackets.
mutual

def size : Json → Nat
  | .null => 1
  | .bool _ => 1
  | .num _ => 1
  | .str _ => 1
  | .arr elems => 2 + sizeList elems.toList
  | .obj fields => 2 + sizeFields fields.toList

def sizeList : List Json → Nat
  | [] => 1
  | j :: rest => size j + 1 + sizeList rest

def sizeFields : List (String × Json) → Nat
  | [] => 1
  | (_, v) :: rest => size v + 1 + sizeFields rest

end

def Item.weight : Item → Nat
  | .lit _ => 1
  | .val _ j => 2 * size j
  | .elems _ l _ => 2 * sizeList l
  | .members _ l _ => 2 * sizeFields l

def weight : List Item → Nat
  | [] => 0
  | i :: rest => i.weight + weight rest

/-- The text that precedes an element or member: nothing for the first, a separator otherwise. -/
def Style.precedes (st : Style) (depth : Nat) (first : Bool) : String :=
  if first then "" else "," ++ st.lineBreak depth

/--
The traversal itself, over an explicit stack of pending output rather than the call stack, so
that a deeply nested value costs heap and cannot overflow. Every step retires one item and
pushes at most two smaller ones.
-/
def render (st : Style) : List Item → String → String
  | [], acc => acc
  | .lit s :: rest, acc => render st rest (acc ++ s)
  | .val _ .null :: rest, acc => render st rest (acc ++ "null")
  | .val _ (.bool true) :: rest, acc => render st rest (acc ++ "true")
  | .val _ (.bool false) :: rest, acc => render st rest (acc ++ "false")
  | .val _ (.num n) :: rest, acc => render st rest (acc ++ number n)
  | .val _ (.str s) :: rest, acc => render st rest (stringTo acc s)
  | .val d (.arr elems) :: rest, acc =>
    if elems.isEmpty then
      render st rest (acc ++ "[]")
    else
      render st (.elems (d + 1) elems.toList true :: .lit (st.lineBreak d ++ "]") :: rest)
        (acc ++ "[" ++ st.lineBreak (d + 1))
  | .val d (.obj fields) :: rest, acc =>
    if fields.isEmpty then
      render st rest (acc ++ "{}")
    else
      render st (.members (d + 1) fields.toList true :: .lit (st.lineBreak d ++ "}") :: rest)
        (acc ++ "{" ++ st.lineBreak (d + 1))
  | .elems _ [] _ :: rest, acc => render st rest acc
  | .elems d (j :: l) first :: rest, acc =>
    render st (.val d j :: .elems d l false :: rest) (acc ++ st.precedes d first)
  | .members _ [] _ :: rest, acc => render st rest acc
  | .members d ((k, v) :: l) first :: rest, acc =>
    render st (.val d v :: .members d l false :: rest)
      (stringTo (acc ++ st.precedes d first) k ++ st.colon)
termination_by items _ => weight items
decreasing_by all_goals simp only [weight, Item.weight, size, sizeList, sizeFields] <;> omega

end

end Json.Printer

namespace Json

@[expose] section

namespace Number

/-- The canonical spelling of `n` as JSON text. -/
def toString (n : Number) : String := Printer.number n

instance : ToString Number := ⟨toString⟩

end Number

/-- The body of a string literal: `s` escaped as RFC 8259 requires, without quotation marks. -/
def escape (s : String) : String := Printer.escapeTo "" s

/-- `s` as a JSON string literal, quotation marks included. -/
def renderString (s : String) : String := Printer.string s

/-- `j` as JSON text with no space beyond what the grammar requires. -/
def compress (j : Json) : String := Printer.render Printer.Style.compact [.val 0 j] ""

/-- `j` as JSON text laid out over several lines, each level indented by `indent` spaces. -/
def pretty (j : Json) (indent : Nat := 2) : String :=
  Printer.render (Printer.Style.pretty indent) [.val 0 j] ""

instance : ToString Json := ⟨compress⟩

end

end Json
