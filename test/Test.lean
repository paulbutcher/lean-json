/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Test.Runner
import Test.Number
import Test.Api
import Test.Basic
import Test.Spec
import Test.Parser
import Test.Printer
import Test.FromTo
import Test.Query
import Test.Stream
import Test.Conformance
import Test.Fuzz
import Test.Regression

namespace Test

-- Each test module contributes its cases here. Modules that consist only of
-- theorems need no entry: compiling them is passing.
def all : Array TestCase :=
  Test.Number.all ++ Test.Parser.all ++ Test.Printer.all ++
    Test.FromTo.all ++ Test.Query.all ++
    Test.Stream.all ++ Test.Conformance.all ++ Test.Fuzz.all ++ Test.Regression.all

end Test
