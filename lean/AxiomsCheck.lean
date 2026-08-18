import Correctness
import Proposals
#print axioms Redgrep.nullable_correct
#print axioms Redgrep.lang_deriv
#print axioms Redgrep.deriv_correct
#print axioms Redgrep.matchRE_correct
#print axioms Redgrep.matchW_correct
#eval Redgrep.matchRE (.invHom (fun c => [c, c]) (.rep (.sym (fun c => c == 'a')))) ['a', 'a']
#eval Redgrep.matchRE (.invHom (fun _ => []) .eps) ['x', 'y']
