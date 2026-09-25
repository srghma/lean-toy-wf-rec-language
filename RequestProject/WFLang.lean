import RequestProject.WFLang.Core.Types
import RequestProject.WFLang.Core.While
import RequestProject.WFLang.Core.PExpr
import RequestProject.WFLang.Core.Normal
import RequestProject.WFLang.PCL.Lang
import RequestProject.WFLang.PCL.Size
import RequestProject.WFLang.PCL.Termination
import RequestProject.WFLang.Capture.Meta
import RequestProject.WFLang.Capture.Optimize
import RequestProject.WFLang.Capture.Translate
import RequestProject.WFLang.Capture.Elab
import RequestProject.WFLang.Tests.Functions
import RequestProject.WFLang.Tests.Basic
import RequestProject.WFLang.Tests.BasicChecks
import RequestProject.WFLang.Tests.MoreFunctions
import RequestProject.WFLang.Tests.More
import RequestProject.WFLang.Tests.MoreChecks
import RequestProject.WFLang.Tests.SourceProofs
import RequestProject.WFLang.Tests.Sources
import RequestProject.WFLang.Tests.GapFunctions
import RequestProject.WFLang.Tests.Gaps
import RequestProject.WFLang.Tests.Joins
import RequestProject.WFLang.Tests.Normal
import RequestProject.WFLang.Tests.Globals
import RequestProject.WFLang.Tests.WhileFunctions
import RequestProject.WFLang.Tests.While

/-!
# PCL: a typed toy language capturing well-founded Lean functions

* `Core/`        types, environments, variables, operators, call-free expressions
* `PCL/`         the language (`fix` + proof-carrying `fixSelfCall`, well-founded `while`), its
                 evaluator and soundness
* `Capture/`     `#lean_wf_func_to_term f` and the `wf_agree` tactic
* `Tests/`       the test suite (captures, agreement theorems, runtime checks, rejections)
-/
