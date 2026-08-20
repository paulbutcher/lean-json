/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Json

/-!
The theorems a caller is told about, named here to check that a caller can reach them.

The README says these are proved, which is a claim about what a client can build on, so each has
to be importable and public. Naming them fails the build if one is renamed or made private, or
moved somewhere a client cannot import, which nothing else here would catch.
-/

namespace Test.Api

example := @Json.beq_iff_eq

example := @Json.Alg.fold_eq_run
example := @Json.beqPairs_eq
example := @Json.hash_eq_run
example := @Json.uniqueKeys_eq_run
example := @Json.canonicalNumbers_eq_run
example := @Json.depth_eq_run

example := @Json.findLast?_push
example := @Json.findLast?_setIfInBounds
example := @Json.distinctNames_iff
example := @Json.findLast?_dedupKeys
example := @Json.distinctNames_dedupKeys
example := @Json.dedupKeys_eq_self
example := @Json.dedupKeys_dedupKeys

example := @Json.get?_set?
example := @Json.set?_get?

example := @Json.depth_arr_lt
example := @Json.depth_obj_lt

example := @Json.json_roundTrip
example := @Json.int_roundTrip
example := @Json.nat_roundTrip
example := @Json.option_some_roundTrip
example := @Json.prod_roundTrip
example := @Json.array_roundTrip
example := @Json.list_roundTrip

example := @Json.Number.eqv_iff_eq
example := @Json.Number.isLt_iff
example := @Json.Number.cmp_eq_compare_scaleTo
example := @Json.Number.pow_digitCount_le
example := @Json.Number.natAbs_lt_pow_digitCount
example := @Json.Number.Eqv.symm
example := @Json.Number.Eqv.trans
example := @Json.Number.canonical_normalize
example := @Json.Number.canonical_ofFloat
example := @Json.Number.cmp_eq_eq_iff_eq
example := @Json.Number.toInt?_ofInt

example := @Json.Parser.remaining_startPos
example := @Json.Parser.remaining_step
example := @Json.Parser.ws_skipWs
example := @Json.Parser.number_sound
example := @Json.Parser.str_sound
example := @Json.Parser.text_parseFrom
example := @Json.Parser.text_parse
example := @Json.Parser.textOf_parseBytes
example := @Json.Parser.eq_of_textOf
example := @Json.Parser.canonicalNumbers_parse
example := @Json.Parser.parse_eq_of_isOk
example := @Json.Parser.skipWs_complete
example := @Json.Parser.uniqueKeys_parse
example := @Json.Parser.parse_complete
example := @Json.Parser.parseFrom_complete
example := @Json.parse_compress
example := @Json.parse_pretty

/-- The headline claim, reached through the entry point a caller actually calls. -/
example {s : String} {j : Json} (h : Json.parse s { ignoreBOM := false } = .ok j) :
    Json.Spec.TextOf s j := Json.Parser.textOf_parse rfl h

/--
The other direction, composed with what it needs: anything read can be written and read back.
Naming it here is what says the round trip theorem's hypothesis is one a caller can discharge.
-/
example {s : String} {j : Json} (h : Json.parse s {} = .ok j) :
    Json.parse (Json.compress j)
        { duplicateKeys := .allow, maxDepth := none, maxNumberDigits := none } = .ok j :=
  Json.parse_compress rfl rfl rfl (Json.Parser.canonicalNumbers_parse h)

example := @Json.Printer.textOf_compress
example := @Json.Printer.textOf_pretty
example := @Json.Printer.spec_renderString
example := @Json.Printer.isValidUTF8_toByteArray

example := @Json.Spec.num_unique
example := @Json.Spec.str_unique
example := @Json.Spec.text_unique
example := @Json.Spec.textOf_unique
example := @Json.Spec.canonicalNumbers_of_text
example := @Json.Spec.value_length

example := @Json.Spec.ws_eq_of_not_isWs
example := @Json.Spec.char_not_surrogate

example := @Array.pushInduction
example := @Array.setIfInBounds_getElem

end Test.Api
