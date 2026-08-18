/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Test.Runner
import Test.Number
import Test.Basic
import Test.Spec
import Test.Parser
import Test.Printer
import Test.Printer.Soundness
import Test.FromTo

namespace Test

-- Each test module contributes its cases here. Modules that consist only of
-- theorems need no entry: compiling them is passing.
def all : Array TestCase :=
  Test.Number.all ++ Test.Basic.all ++ Test.Parser.all ++ Test.Printer.all ++ Test.FromTo.all

end Test
