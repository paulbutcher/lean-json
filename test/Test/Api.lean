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

example := @Json.Number.eqv_iff_eq
example := @Json.Number.Eqv.symm
example := @Json.Number.Eqv.trans
example := @Json.Number.canonical_normalize
example := @Json.Number.canonical_ofFloat
example := @Json.Number.cmp_eq_eq_iff_eq

example := @Json.Printer.textOf_compress
example := @Json.Printer.textOf_pretty
example := @Json.Printer.spec_renderString
example := @Json.Printer.isValidUTF8_toByteArray

example := @Json.Spec.ws_eq_of_not_isWs
example := @Json.Spec.char_not_surrogate

example := @Array.pushInduction
example := @Array.setIfInBounds_getElem

end Test.Api
