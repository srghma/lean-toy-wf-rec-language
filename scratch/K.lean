import RequestProject.WFLang.PCL.Lang
open WFLang WFLang.PCL
example (Γ : List Ty) (t s : Ty) (x : Join Γ t) (e : Env Γ) (w : s.denote) (J : JoinVal x e) (v : x.arg.denote) (hv : x.pre (x.cur e) v) :
  ((JVar.here : JVar ([x].map (·.push s)) (x.push s)).get (JEnv.push (v := w) ((J, ()) : JEnv [x] e)) v hv).1 = (J v hv).1 := by
  simp
