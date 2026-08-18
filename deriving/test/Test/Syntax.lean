/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import JsonDeriving
import Test.Runner
import Test.Codecs

open Json

namespace Test.Syntax

private def renders (name : String) (j : Json) (expected : String) : TestCase :=
  expectEq name (compress j) expected

private def here : Test.Codecs.Point := { x := 1, y := 2 }

def all : Array TestCase := #[
  renders "null" (json% null) "null",
  renders "true" (json% true) "true",
  renders "false" (json% false) "false",
  renders "a whole number" (json% 42) "42",
  renders "a number with a fraction and an exponent" (json% 1.5e2) "150",
  renders "a negative number" (json% -3) "-3",
  renders "a negative number with a fraction" (json% -0.25) "-0.25",
  renders "a string" (json% "hi") "\"hi\"",
  renders "an array" (json% [1, "a", null]) "[1,\"a\",null]",
  renders "an object with bare names" (json% {a: 1, b: [true]}) "{\"a\":1,\"b\":[true]}",
  -- A name that is not an identifier is written as a string, as it would be in JSON.
  renders "an object with a quoted name" (json% {"a b": 1}) "{\"a b\":1}",
  renders "nesting" (json% {a: {b: [{c: null}]}}) "{\"a\":{\"b\":[{\"c\":null}]}}",
  -- The escape hatch: a Lean term, encoded by whatever instance it has.
  renders "a computed value" (json% $(2 + 3)) "5",
  renders "a derived instance in a literal" (json% {home: $(here)}) "{\"home\":{\"x\":1,\"y\":2}}",
  renders "the empty object and array" (json% {}) "{}",
  renders "an empty array" (json% []) "[]"
]

end Test.Syntax
