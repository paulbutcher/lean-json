/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Json.Printer
public import Json.Spec

public section

namespace Json.Printer

/-!
What the printer emits, stated against the grammar rather than against the printer.

The printer runs over an explicit stack, which is what keeps it safe on deep values but leaves
its output related to the value only through a loop invariant. So the text is described a second
time by structural recursion, `chars`, and the two are proved to agree; the grammar theorems are
then stated about `chars`, where induction follows the shape of the value. Only the claims a
caller can use are exported; the description and the per-production lemmas are the scaffolding
that reaches them.
-/

/-! ## The same output, described by recursion on the value -/

mutual

private def chars (st : Style) (depth : Nat) : Json → List Char
  | .null => "null".toList
  | .bool true => "true".toList
  | .bool false => "false".toList
  | .num n => (number n).toList
  | .str s => (string s).toList
  | .arr elems =>
    if elems.isEmpty then "[]".toList
    else ("[" ++ st.lineBreak (depth + 1)).toList ++ elemChars st (depth + 1) elems.toList true ++
      (st.lineBreak depth ++ "]").toList
  | .obj fields =>
    if fields.isEmpty then "{}".toList
    else ("{" ++ st.lineBreak (depth + 1)).toList ++
      memberChars st (depth + 1) fields.toList true ++ (st.lineBreak depth ++ "}").toList

private def elemChars (st : Style) (depth : Nat) : List Json → Bool → List Char
  | [], _ => []
  | j :: l, first =>
    (st.precedes depth first).toList ++ chars st depth j ++ elemChars st depth l false

private def memberChars (st : Style) (depth : Nat) : List (String × Json) → Bool → List Char
  | [], _ => []
  | (k, v) :: l, first =>
    (st.precedes depth first).toList ++ (string k).toList ++ st.colon.toList ++
      chars st depth v ++ memberChars st depth l false

end

private def itemChars (st : Style) : Item → List Char
  | .lit s => s.toList
  | .val d j => chars st d j
  | .elems d l first => elemChars st d l first
  | .members d l first => memberChars st d l first

private def itemsChars (st : Style) : List Item → List Char
  | [] => []
  | i :: rest => itemChars st i ++ itemsChars st rest

/-! ## Agreement -/

/-- The characters a string contributes inside a literal. -/
private def escapeCharsOf (l : List Char) : List Char := (l.map escapeChars).flatten

private theorem toList_escapeCharTo (acc : String) (c : Char) :
    (escapeCharTo acc c).toList = acc.toList ++ escapeChars c := by
  fun_cases escapeCharTo acc c <;> simp [escapeChars] <;> omega

private theorem toList_foldl_escape (l : List Char) (acc : String) :
    (l.foldl escapeCharTo acc).toList = acc.toList ++ escapeCharsOf l := by
  induction l generalizing acc with
  | nil => simp [escapeCharsOf]
  | cons c cs ih => simp [ih, toList_escapeCharTo, escapeCharsOf]

private theorem toList_escapeTo (acc s : String) :
    (escapeTo acc s).toList = acc.toList ++ escapeCharsOf s.toList := by
  simp [escapeTo, String.foldl_eq_foldl_toList, toList_foldl_escape]

private theorem toList_string (s : String) :
    (string s).toList = '"' :: (escapeCharsOf s.toList ++ ['"']) := by
  simp [string, stringTo, String.toList_push, toList_escapeTo]

private theorem toList_stringTo (acc s : String) :
    (stringTo acc s).toList = acc.toList ++ (string s).toList := by
  simp [stringTo, String.toList_push, toList_escapeTo, toList_string]

/-! ## Digits -/

/-- The value a run of digit characters denotes. -/
private def digitsValue : List Char → Nat
  | [] => 0
  | c :: cs => Spec.digitVal c * 10 ^ cs.length + digitsValue cs

private theorem digitsValue_append (l₁ l₂ : List Char) :
    digitsValue (l₁ ++ l₂) = digitsValue l₁ * 10 ^ l₂.length + digitsValue l₂ := by
  induction l₁ with
  | nil => simp [digitsValue]
  | cons c cs ih =>
    simp only [List.cons_append, digitsValue, ih, List.length_append, Nat.pow_add,
      Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]

private theorem hexVal_hexDigitChar {d : Nat} (h : d < 16) :
    Spec.hexVal? (hexDigitChar d) = some d :=
  (by decide : ∀ d ∈ List.range 16, Spec.hexVal? (hexDigitChar d) = some d) d
    (List.mem_range.mpr h)

private theorem isDigit_digitChar {d : Nat} (h : d < 10) : Spec.isDigit (digitChar d) = true :=
  (by decide : ∀ d ∈ List.range 10, Spec.isDigit (digitChar d) = true) d (List.mem_range.mpr h)

private theorem digitVal_digitChar {d : Nat} (h : d < 10) : Spec.digitVal (digitChar d) = d :=
  (by decide : ∀ d ∈ List.range 10, Spec.digitVal (digitChar d) = d) d (List.mem_range.mpr h)

private theorem digitCharsTo_eq (n : Nat) : ∀ acc, digitCharsTo n acc = digitChars n ++ acc := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro acc
    by_cases h : n < 10
    · rw [digitCharsTo, if_pos h, digitChars, digitCharsTo, if_pos h]
      simp
    · have hr : digitChars n = digitCharsTo (n / 10) [digitChar (n % 10)] := by
        rw [digitChars, digitCharsTo, if_neg h]
      rw [digitCharsTo, if_neg h, hr, ih (n / 10) (by omega), ih (n / 10) (by omega)]
      simp

private theorem digitChars_of_lt {n : Nat} (h : n < 10) : digitChars n = [digitChar n] := by
  rw [digitChars, digitCharsTo, if_pos h]

private theorem digitChars_of_le {n : Nat} (h : 10 ≤ n) :
    digitChars n = digitChars (n / 10) ++ [digitChar (n % 10)] := by
  rw [digitChars, digitCharsTo, if_neg (by omega), digitCharsTo_eq]

private theorem digitChars_ne_nil (n : Nat) : digitChars n ≠ [] := by
  by_cases h : n < 10
  · simp [digitChars_of_lt h]
  · simp [digitChars_of_le (show 10 ≤ n by omega)]

private theorem isDigit_of_mem_digitChars (n : Nat) :
    ∀ c ∈ digitChars n, Spec.isDigit c = true := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h : n < 10
    · simp only [digitChars_of_lt h, List.mem_singleton]
      intro c hc
      exact hc ▸ isDigit_digitChar h
    · simp only [digitChars_of_le (by omega : 10 ≤ n), List.mem_append, List.mem_singleton]
      intro c hc
      rcases hc with hc | hc
      · exact ih (n / 10) (by omega) c hc
      · exact hc ▸ isDigit_digitChar (by omega)

private theorem digitsValue_digitChars (n : Nat) : digitsValue (digitChars n) = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h : n < 10
    · simp [digitChars_of_lt h, digitsValue, digitVal_digitChar h]
    · rw [digitChars_of_le (by omega : 10 ≤ n), digitsValue_append,
        ih (n / 10) (by omega)]
      simp [digitsValue, digitVal_digitChar (show n % 10 < 10 by omega)]
      omega

private theorem head_digitChars {n : Nat} (h : 1 ≤ n) :
    ∃ c cs, digitChars n = c :: cs ∧ ('1' ≤ c && c ≤ '9') = true := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases hlt : n < 10
    · refine ⟨digitChar n, [], digitChars_of_lt hlt, ?_⟩
      exact (by decide : ∀ d ∈ List.range' 1 9, ('1' ≤ digitChar d && digitChar d ≤ '9') = true) n
        (List.mem_range'_1.mpr ⟨h, by omega⟩)
    · obtain ⟨c, cs, hc, hrange⟩ := ih (n / 10) (by omega) (by omega)
      exact ⟨c, cs ++ [digitChar (n % 10)], by
        rw [digitChars_of_le (by omega : 10 ≤ n), hc, List.cons_append], hrange⟩

private theorem spec_digits {l : List Char} (hd : ∀ c ∈ l, Spec.isDigit c = true) (hne : l ≠ [])
    (r : List Char) : Spec.Digits (l ++ r) (digitsValue l) l.length r := by
  induction l with
  | nil => exact absurd rfl hne
  | cons c cs ih =>
    match cs with
    | [] => simpa [digitsValue] using Spec.Digits.last (r := r) (hd c (by simp))
    | c' :: cs' =>
      exact Spec.Digits.cons (hd c (by simp))
        (ih (fun x hx => hd x (by simp [hx])) (by simp))

private theorem append_ne_nil_of_right {l₁ l₂ : List Char} (h : l₂ ≠ []) : l₁ ++ l₂ ≠ [] := by
  cases l₁ <;> simp_all

private theorem spec_digits_append {l₁ l₂ r : List Char}
    (h₁ : ∀ c ∈ l₁, Spec.isDigit c = true) (h₂ : ∀ c ∈ l₂, Spec.isDigit c = true)
    (hne : l₁ ++ l₂ ≠ []) :
    Spec.Digits (l₁ ++ (l₂ ++ r)) (digitsValue l₁ * 10 ^ l₂.length + digitsValue l₂)
      (l₁.length + l₂.length) r := by
  have h := spec_digits (l := l₁ ++ l₂)
    (fun c hc => by
      rcases List.mem_append.mp hc with h | h
      · exact h₁ c h
      · exact h₂ c h) hne r
  rw [List.append_assoc] at h
  simpa [digitsValue_append] using h

private theorem spec_int' {l : List Char} (hd : ∀ c ∈ l, Spec.isDigit c = true)
    (hhead : ∃ c cs, l = c :: cs ∧ ('1' ≤ c && c ≤ '9') = true) (r : List Char) :
    Spec.Int' (l ++ r) (digitsValue l) r := by
  obtain ⟨c, cs, hl, hrange⟩ := hhead
  subst hl
  exact Spec.Int'.digits hrange (spec_digits hd (by simp) r)

private theorem isDigit_of_mem_zeros (k : Nat) :
    ∀ c ∈ List.replicate k '0', Spec.isDigit c = true := by
  intro c hc
  rw [List.eq_of_mem_replicate hc]
  decide

private theorem digitsValue_zeros (k : Nat) : digitsValue (List.replicate k '0') = 0 := by
  induction k with
  | zero => simp [digitsValue]
  | succ k ih => simp [List.replicate_succ, digitsValue, ih, Spec.digitVal]

/-! ## Numbers -/

private theorem toList_sign (m : Int) :
    ((if m < 0 then "-" else "" : String)).toList = (if m < 0 then ['-'] else []) := by
  by_cases h : m < 0 <;> simp [h]

/-- Rescaling the mantissa by a power of ten leaves the normal form alone. -/
private theorem normalize_mul_pow (m : Int) (k : Nat) :
    Number.normalize (m * 10 ^ k) 0 = Number.normalize m k :=
  Number.eqv_iff_normalize_eq.mp <| by
    show Number.Eqv ⟨m * 10 ^ k, 0⟩ ⟨m, (k : Int)⟩
    have h : ((k : Int) - min 0 (k : Int)).toNat = k := by omega
    have h0 : ((0 : Int) - min 0 (k : Int)).toNat = 0 := by omega
    simp only [Number.Eqv, Number.scaleTo, h, h0, Int.pow_zero, Int.mul_one]

/-- Each branch of `number` is a sign followed by the same four productions. -/
private theorem spec_num_of {m : Int} {text r s₂ s₃ : List Char} {i f nf : Nat} {e : Int}
    {target : Number}
    (hi : Spec.Int' text i s₂) (hf : Spec.Frac s₂ f nf s₃) (he : Spec.Exp s₃ e r)
    (hv : Number.normalize
      (if m < 0 then -((i * 10 ^ nf + f : Nat) : Int) else ((i * 10 ^ nf + f : Nat) : Int))
      (e - nf) = target) :
    Spec.Num ((if m < 0 then ['-'] else []) ++ text) target r := by
  subst hv
  by_cases h : m < 0
  · simpa [h] using Spec.Num.mk (neg := true) Spec.Sign.minus hi hf he
  · simpa [h] using Spec.Num.mk (neg := false) Spec.Sign.absent hi hf he

private theorem spec_num (n : Number) (r : List Char) :
    Spec.Num ((number n).toList ++ r) (Number.normalize n.mantissa n.exponent) r := by
  by_cases hm : n.mantissa = 0
  · simp only [number, if_pos hm]
    have hz : Number.normalize n.mantissa n.exponent = Number.normalize 0 0 := by
      simp [Number.normalize, hm]
    rw [hz]
    simpa using Spec.Num.mk (neg := false) (s₁ := '0' :: r) Spec.Sign.absent Spec.Int'.zero
      Spec.Frac.absent Spec.Exp.absent
  · have hd := isDigit_of_mem_digitChars n.mantissa.natAbs
    have hval := digitsValue_digitChars n.mantissa.natAbs
    have hhead := head_digitChars (show 1 ≤ n.mantissa.natAbs by omega)
    simp only [number, if_neg hm]
    by_cases he0 : n.exponent = 0
    · rw [if_pos he0]
      simp only [String.toList_append, String.toList_ofList, toList_sign, List.append_assoc]
      refine spec_num_of (hval ▸ spec_int' hd hhead r) Spec.Frac.absent Spec.Exp.absent ?_
      rw [he0]
      simp only [Nat.pow_zero, Nat.mul_one, Nat.add_zero]
      congr 1
      omega
    · have hsign : (if n.mantissa < 0 then -((n.mantissa.natAbs : Int))
          else ((n.mantissa.natAbs : Int))) = n.mantissa := by
        by_cases h : n.mantissa < 0 <;> simp only [h, if_true, if_false] <;> omega
      rw [if_neg he0]
      by_cases hpos : 0 < n.exponent
      · rw [if_pos hpos]
        by_cases hlim : n.exponent ≤ (plainZeroLimit : Int)
        · -- Plain decimal with trailing zeros: the padding belongs to the integer part.
          rw [if_pos hlim]
          simp only [String.toList_append, String.toList_ofList, toList_sign, zeros,
            List.append_assoc]
          obtain ⟨c, cs, hc, hrange⟩ := hhead
          have hi := spec_int'
            (l := digitChars n.mantissa.natAbs ++ List.replicate n.exponent.toNat '0')
            (fun x hx => by
              rcases List.mem_append.mp hx with h | h
              · exact isDigit_of_mem_digitChars _ x h
              · exact isDigit_of_mem_zeros _ x h)
            ⟨c, cs ++ List.replicate n.exponent.toNat '0', by rw [hc, List.cons_append],
              hrange⟩ r
          rw [List.append_assoc, digitsValue_append, hval, digitsValue_zeros, Nat.add_zero,
            List.length_replicate] at hi
          refine spec_num_of hi Spec.Frac.absent Spec.Exp.absent ?_
          simp only [Nat.pow_zero, Nat.mul_one, Nat.add_zero]
          have hcast : (if n.mantissa < 0
              then -((n.mantissa.natAbs * 10 ^ n.exponent.toNat : Nat) : Int)
              else ((n.mantissa.natAbs * 10 ^ n.exponent.toNat : Nat) : Int))
              = n.mantissa * 10 ^ n.exponent.toNat := by
            by_cases h : n.mantissa < 0
            · simp only [if_pos h, Int.natCast_mul, Int.natCast_pow, ← Int.neg_mul]
              congr 1
              omega
            · simp only [if_neg h, Int.natCast_mul, Int.natCast_pow]
              congr 1
              omega
          rw [hcast, show ((0 : Int) - ((0 : Nat) : Int)) = 0 from by omega, normalize_mul_pow]
          congr 1
          omega
        · -- Exponent notation, the padding being too long to write out.
          rw [if_neg hlim, if_neg (show ¬n.exponent < 0 by omega)]
          simp only [String.toList_append, String.toList_ofList, toList_sign, digitString,
            List.append_assoc]
          refine spec_num_of (hval ▸ spec_int' hd hhead _) Spec.Frac.absent
            (Spec.Exp.bare (Or.inl rfl)
              ((digitsValue_digitChars n.exponent.toNat) ▸
                spec_digits (isDigit_of_mem_digitChars _) (digitChars_ne_nil _) r)) ?_
          simp only [Nat.pow_zero, Nat.mul_one, Nat.add_zero]
          rw [hsign]
          congr 1
          omega
      · by_cases hk : (-n.exponent).toNat < (digitChars n.mantissa.natAbs).length
        · -- A decimal point inside the digits.
          rw [if_neg hpos, if_pos hk]
          simp only [String.toList_append, String.toList_ofList, toList_sign, List.append_assoc]
          obtain ⟨c, cs, hc, hrange⟩ := hhead
          obtain ⟨j, hjdef⟩ : ∃ j, (digitChars n.mantissa.natAbs).length -
              (-n.exponent).toNat = j + 1 :=
            ⟨(digitChars n.mantissa.natAbs).length - (-n.exponent).toNat - 1, by omega⟩
          rw [hjdef]
          have htake : (digitChars n.mantissa.natAbs).take (j + 1) = c :: cs.take j := by
            rw [hc, List.take_succ_cons]
          have hdroplen : ((digitChars n.mantissa.natAbs).drop (j + 1)).length =
              (-n.exponent).toNat := by
            rw [List.length_drop]
            omega
          have hi := spec_int' (l := (digitChars n.mantissa.natAbs).take (j + 1))
            (fun x hx => isDigit_of_mem_digitChars _ x (List.mem_of_mem_take hx))
            ⟨c, _, htake, hrange⟩
            ('.' :: ((digitChars n.mantissa.natAbs).drop (j + 1) ++ r))
          refine spec_num_of hi
            (Spec.Frac.present (spec_digits
              (fun x hx => isDigit_of_mem_digitChars _ x (List.mem_of_mem_drop hx))
              (by simp only [ne_eq, List.eq_nil_iff_length_eq_zero, hdroplen]; omega) r))
            Spec.Exp.absent ?_
          rw [hdroplen, show digitsValue ((digitChars n.mantissa.natAbs).take (j + 1)) *
              10 ^ (-n.exponent).toNat +
              digitsValue ((digitChars n.mantissa.natAbs).drop (j + 1)) = n.mantissa.natAbs from by
            rw [← hdroplen, ← digitsValue_append, List.take_append_drop, hval], hsign]
          congr 1
          omega
        · by_cases hz : (-n.exponent).toNat - (digitChars n.mantissa.natAbs).length
              ≤ plainZeroLimit
          · -- A zero integer part, and a fraction that starts with padding.
            rw [if_neg hpos, if_neg hk, if_pos hz]
            simp only [String.toList_append, String.toList_ofList, toList_sign, zeros,
              List.append_assoc]
            refine spec_num_of Spec.Int'.zero
              (Spec.Frac.present (spec_digits_append
                (l₁ := List.replicate ((-n.exponent).toNat -
                  (digitChars n.mantissa.natAbs).length) '0')
                (l₂ := digitChars n.mantissa.natAbs)
                (isDigit_of_mem_zeros _) (isDigit_of_mem_digitChars _)
                (append_ne_nil_of_right (digitChars_ne_nil _)))) Spec.Exp.absent ?_
            rw [digitsValue_zeros, hval, List.length_replicate, Nat.zero_mul, Nat.zero_add,
              Nat.zero_mul, Nat.zero_add,
              show (-n.exponent).toNat - (digitChars n.mantissa.natAbs).length +
                (digitChars n.mantissa.natAbs).length = (-n.exponent).toNat from by omega,
              hsign]
            congr 1
            omega
          · -- Exponent notation again, this time with a negative exponent.
            rw [if_neg hpos, if_neg hk, if_neg hz, if_pos (show n.exponent < 0 by omega)]
            simp only [String.toList_append, String.toList_ofList, toList_sign, digitString,
              List.append_assoc]
            refine spec_num_of (hval ▸ spec_int' hd hhead _) Spec.Frac.absent
              (Spec.Exp.minus (Or.inl rfl)
                ((digitsValue_digitChars (-n.exponent).toNat) ▸
                  spec_digits (isDigit_of_mem_digitChars _) (digitChars_ne_nil _) r)) ?_
            simp only [Nat.pow_zero, Nat.mul_one, Nat.add_zero]
            rw [hsign]
            congr 1
            omega

/-! ## Strings -/

private theorem spec_ch (c : Char) (r : List Char) : Spec.Ch (escapeChars c ++ r) c r := by
  fun_cases escapeChars c
  case case1 => exact .quote
  case case2 => exact .backslash
  case case3 => exact .backspace
  case case4 => exact .formFeed
  case case5 => exact .lineFeed
  case case6 => exact .carriageReturn
  case case7 => exact .tab
  case case8 =>
    rename_i hctrl
    refine Spec.Ch.codePoint (v := 0 * 4096 + 0 * 256 + c.toNat / 16 * 16 + c.toNat % 16)
      (Spec.Hex4.mk (by decide) (by decide) (hexVal_hexDigitChar (by omega))
        (hexVal_hexDigitChar (by omega))) (by omega)
  case case9 =>
    rename_i h1 h2 _ _ _ _ _ _
    refine Spec.Ch.unescaped ?_
    have h34 : c.toNat ≠ 34 := fun h => h1 (Char.toNat_inj.mp (by rw [h]; rfl))
    have h92 : c.toNat ≠ 92 := fun h => h2 (Char.toNat_inj.mp (by rw [h]; rfl))
    simp only [Spec.isUnescaped, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    omega

private theorem spec_chars (l r : List Char) : Spec.Chars (escapeCharsOf l ++ r) l r := by
  induction l with
  | nil => simpa [escapeCharsOf] using Spec.Chars.nil (r := r)
  | cons c cs ih =>
    have h := Spec.Chars.cons (spec_ch c (escapeCharsOf cs ++ r)) ih
    simpa [escapeCharsOf, List.append_assoc] using h

private theorem spec_str (s : String) (r : List Char) : Spec.Str ((string s).toList ++ r) s r := by
  rw [toList_string]
  have h := Spec.Str.mk (spec_chars s.toList ('"' :: r))
  rw [String.ofList_toList] at h
  simpa using h

/-! ## Whitespace and structural characters -/

private theorem ws_spaces (n : Nat) (x : List Char) : Spec.Ws ((spaces n).toList ++ x) x := by
  simp only [spaces, String.toList_ofList]
  induction n with
  | zero => simpa using Spec.Ws.nil (r := x)
  | succ n ih => exact List.replicate_succ ▸ Spec.Ws.cons (by decide) ih

private theorem ws_lineBreak (st : Style) (d : Nat) (x : List Char) :
    Spec.Ws ((st.lineBreak d).toList ++ x) x := by
  unfold Style.lineBreak
  split
  · simpa using Spec.Ws.nil (r := x)
  · simpa [String.toList_append] using Spec.Ws.cons (c := '\n') (by decide) (ws_spaces _ x)

/-- An opening or separating character, which our layout never precedes with space. -/
private theorem token_before (t : Char) (st : Style) (d : Nat) (x : List Char) :
    Spec.Token t (t :: ((st.lineBreak d).toList ++ x)) x :=
  Spec.Token.mk Spec.Ws.nil (ws_lineBreak st d x)

/-- A closing character, which the layout may precede with a break. -/
private theorem token_after (t : Char) (st : Style) (d : Nat) (x : List Char) :
    Spec.Token t ((st.lineBreak d).toList ++ (t :: x)) x :=
  Spec.Token.mk (ws_lineBreak st d (t :: x)) Spec.Ws.nil

private theorem token_colon (st : Style) (x : List Char) :
    Spec.NameSeparator (st.colon.toList ++ x) x := by
  unfold Style.colon
  split
  · simpa using Spec.Token.mk (t := ':') Spec.Ws.nil Spec.Ws.nil
  · exact Spec.Token.mk (s' := ' ' :: x) (by simpa using Spec.Ws.nil (r := ':' :: ' ' :: x))
      (Spec.Ws.cons (by decide) Spec.Ws.nil)

private theorem token_separator (st : Style) (d : Nat) (x : List Char) :
    Spec.ValueSeparator ((st.precedes d false).toList ++ x) x := by
  simpa [Style.precedes, String.toList_append] using token_before ',' st d x

private theorem toList_render (st : Style) (items : List Item) (acc : String) :
    (render st items acc).toList = acc.toList ++ itemsChars st items := by
  fun_induction render st items acc <;>
    simp_all [itemsChars, itemChars, chars, elemChars, memberChars, toList_stringTo]

/-! ## Well-formedness -/

private theorem toList_precedes_true (st : Style) (d : Nat) : (st.precedes d true).toList = [] := by
  simp [Style.precedes]

mutual

private theorem spec_value (st : Style) (d : Nat) : ∀ (j : Json), canonicalNumbers j = true →
    ∀ r, Spec.Value (chars st d j ++ r) j r
  | .null, _, r => by simpa [chars] using Spec.Value.null (r := r)
  | .bool true, _, r => by simpa [chars] using Spec.Value.true_ (r := r)
  | .bool false, _, r => by simpa [chars] using Spec.Value.false_ (r := r)
  | .num n, h, r => by
    have hc : n.Canonical := of_decide_eq_true (by simpa [canonicalNumbers] using h)
    exact Spec.Value.num (by simpa [chars, Number.normalize_eq_self hc] using spec_num n r)
  | .str s, _, r => by exact Spec.Value.str (by simpa [chars] using spec_str s r)
  | .arr elems, h, r => by
    by_cases he : elems.isEmpty
    · obtain rfl : _ = #[] := Array.empty_of_isEmpty he
      refine Spec.Value.arr (Spec.Arr.empty (s' := ']' :: r) ?_ ?_)
      · simpa [chars] using Spec.Token.mk (t := '[') Spec.Ws.nil Spec.Ws.nil
      · simpa using Spec.Token.mk (t := ']') Spec.Ws.nil Spec.Ws.nil
    · have hne : elems.toList ≠ [] := by
        intro h0
        rw [Array.toList_inj.mp (show elems.toList = (#[] : Array Json).toList by simp [h0])] at he
        simp at he
      have harr := Spec.Arr.items (vs := elems.toList)
        (token_before '[' st (d + 1)
          (elemChars st (d + 1) elems.toList true ++ ((st.lineBreak d).toList ++ (']' :: r))))
        (spec_elements st (d + 1) elems.toList (by simpa [canonicalNumbers] using h) hne
          ((st.lineBreak d).toList ++ (']' :: r)))
        (token_after ']' st d r)
      rw [Array.toArray_toList] at harr
      refine Spec.Value.arr ?_
      have hchars : chars st d (.arr elems) =
          ("[" ++ st.lineBreak (d + 1)).toList ++ elemChars st (d + 1) elems.toList true ++
            (st.lineBreak d ++ "]").toList := by
        rw [chars, if_neg he]
      rw [hchars]
      simpa [String.toList_append, List.append_assoc] using harr
  | .obj fields, h, r => by
    by_cases he : fields.isEmpty
    · obtain rfl : _ = #[] := Array.empty_of_isEmpty he
      refine Spec.Value.obj (Spec.Object.empty (s' := '}' :: r) ?_ ?_)
      · simpa [chars] using Spec.Token.mk (t := '{') Spec.Ws.nil Spec.Ws.nil
      · simpa using Spec.Token.mk (t := '}') Spec.Ws.nil Spec.Ws.nil
    · have hne : fields.toList ≠ [] := by
        intro h0
        rw [Array.toList_inj.mp
          (show fields.toList = (#[] : Array (String × Json)).toList by simp [h0])] at he
        simp at he
      have hobj := Spec.Object.members (ms := fields.toList)
        (token_before '{' st (d + 1)
          (memberChars st (d + 1) fields.toList true ++ ((st.lineBreak d).toList ++ ('}' :: r))))
        (spec_members st (d + 1) fields.toList (by simpa [canonicalNumbers] using h) hne
          ((st.lineBreak d).toList ++ ('}' :: r)))
        (token_after '}' st d r)
      rw [Array.toArray_toList] at hobj
      refine Spec.Value.obj ?_
      have hchars : chars st d (.obj fields) =
          ("{" ++ st.lineBreak (d + 1)).toList ++ memberChars st (d + 1) fields.toList true ++
            (st.lineBreak d ++ "}").toList := by
        rw [chars, if_neg he]
      rw [hchars]
      simpa [String.toList_append, List.append_assoc] using hobj

private theorem spec_elements (st : Style) (d : Nat) :
    ∀ (l : List Json), canonicalNumbersList l = true →
    l ≠ [] → ∀ r, Spec.Elements (elemChars st d l true ++ r) l r
  | [], _, hne, _ => absurd rfl hne
  | [j], h, _, r => by
    have hj : canonicalNumbers j = true := by simpa [canonicalNumbersList] using h
    simpa [elemChars, toList_precedes_true] using
      Spec.Elements.one (spec_value st d j hj r)
  | j :: j' :: rest, h, _, r => by
    obtain ⟨hj, hrest⟩ : canonicalNumbers j = true ∧ canonicalNumbersList (j' :: rest) = true := by
      simpa [canonicalNumbersList, Bool.and_eq_true] using h
    have hmore := Spec.Elements.more
      (spec_value st d j hj
        ((st.precedes d false).toList ++ (elemChars st d (j' :: rest) true ++ r)))
      (token_separator st d (elemChars st d (j' :: rest) true ++ r))
      (spec_elements st d (j' :: rest) hrest (by simp) r)
    simpa [elemChars, toList_precedes_true, List.append_assoc] using hmore

private theorem spec_members (st : Style) (d : Nat) : ∀ (l : List (String × Json)),
    canonicalNumbersFields l = true → l ≠ [] → ∀ r,
      Spec.Members (memberChars st d l true ++ r) l r
  | [], _, hne, _ => absurd rfl hne
  | [(k, v)], h, _, r => by
    have hv : canonicalNumbers v = true := by simpa [canonicalNumbersFields] using h
    have hmem := Spec.Member.mk (spec_str k (st.colon.toList ++ (chars st d v ++ r)))
      (token_colon st (chars st d v ++ r)) (spec_value st d v hv r)
    simpa [memberChars, toList_precedes_true, List.append_assoc] using
      Spec.Members.one hmem
  | (k, v) :: kv' :: rest, h, _, r => by
    obtain ⟨hv, hrest⟩ :
        canonicalNumbers v = true ∧ canonicalNumbersFields (kv' :: rest) = true := by
      simpa [canonicalNumbersFields, Bool.and_eq_true] using h
    have hmem := Spec.Member.mk
      (spec_str k (st.colon.toList ++ (chars st d v ++ ((st.precedes d false).toList ++
        (memberChars st d (kv' :: rest) true ++ r)))))
      (token_colon st (chars st d v ++ ((st.precedes d false).toList ++
        (memberChars st d (kv' :: rest) true ++ r))))
      (spec_value st d v hv ((st.precedes d false).toList ++
        (memberChars st d (kv' :: rest) true ++ r)))
    have hmore := Spec.Members.more hmem
      (token_separator st d (memberChars st d (kv' :: rest) true ++ r))
      (spec_members st d (kv' :: rest) hrest (by simp) r)
    simpa [memberChars, toList_precedes_true, List.append_assoc] using hmore

end

/-! ## What the printer emits is JSON text -/

private theorem toList_compress (j : Json) : (compress j).toList = chars Style.compact 0 j := by
  simp [compress, toList_render, itemsChars, itemChars]

private theorem toList_pretty (j : Json) (indent : Nat) :
    (pretty j indent).toList = chars (Style.pretty indent) 0 j := by
  simp [pretty, toList_render, itemsChars, itemChars]

private theorem spec_text (st : Style) {j : Json} (h : CanonicalNumbers j) :
    Spec.Text (chars st 0 j) j :=
  ⟨chars st 0 j, [], Spec.Ws.nil, by simpa using spec_value st 0 j h [], Spec.Ws.nil⟩

/-- The compressed form of a value is JSON text denoting that value. -/
theorem textOf_compress {j : Json} (h : CanonicalNumbers j) : Spec.TextOf (compress j) j := by
  rw [Spec.TextOf, toList_compress]
  exact spec_text Style.compact h

/-- The laid-out form is JSON text denoting the same value, so the space is never significant. -/
theorem textOf_pretty {j : Json} (h : CanonicalNumbers j) (indent : Nat) :
    Spec.TextOf (pretty j indent) j := by
  rw [Spec.TextOf, toList_pretty]
  exact spec_text (Style.pretty indent) h

/-- A rendered string is a string literal denoting the string it came from, whatever it holds. -/
theorem spec_renderString (s : String) (r : List Char) :
    Spec.Str ((renderString s).toList ++ r) s r := spec_str s r

/--
Anything the printer emits is valid UTF-8, and so meets RFC 8259 section 8.1: it is a `String`,
whose bytes are by definition the UTF-8 encoding of its characters.
-/
theorem isValidUTF8_toByteArray (s : String) : s.toByteArray.IsValidUTF8 :=
  String.utf8Encode_toList ▸ ByteArray.isValidUTF8_utf8Encode
end Json.Printer
