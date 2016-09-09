theory MDEAK_Core_SE
imports Main
begin


(* Operational level *)

type_synonym Atprop = string
type_synonym Agent = string
type_synonym Funaction = string

datatype Action =  Action_Fdiam3 Agent Funaction (infix "\<triangle>\<^sub>3" 330)
                 | Action_Bdiam3 Agent Funaction (infix "\<triangleq>\<^sub>3" 330)

datatype Formula = Formula_Atprop Atprop ("_ \<^sub>F" [320] 330)
                 | Formula_Top ("\<top>")
                 | Formula_Bot ("\<bottom>")
                 | Formula_And Formula Formula (infix "\<and>\<^sub>F" 330)
                 | Formula_Or Formula Formula (infix "\<or>\<^sub>F" 330)
                 | Formula_ImpR Formula Formula (infix "\<rightarrow>\<^sub>F" 330)
                 | Formula_ImpL Formula Formula (infix "\<leftarrow>\<^sub>F" 330)
                 | Formula_DImpR Formula Formula (infix ">-" 330)
                 | Formula_DImpL Formula Formula (infix "-<" 330)
  
                 | Formula_Fdiam0 Funaction Formula (infix "\<triangle>\<^sub>0" 330)
                 | Formula_Fbox0 Funaction Formula (infix "\<rhd>\<^sub>0" 330)
                 | Formula_Fdiam1 Action Formula (infix "\<triangle>\<^sub>1" 330)
                 | Formula_Fbox1 Action Formula (infix "\<rhd>\<^sub>1" 330)
                 | Formula_Fdiam2 Agent Formula (infix "\<triangle>\<^sub>2" 330)
                 | Formula_Fbox2 Agent Formula (infix "\<rhd>\<^sub>2" 330)

                 | Formula_Bdiam0 Funaction Formula (infix "\<triangleq>\<^sub>0" 330)
                 | Formula_Bbox0 Funaction Formula (infix "\<unrhd>\<^sub>0" 330)
                 | Formula_Bdiam1 Action Formula (infix "\<triangleq>\<^sub>1" 330)
                 | Formula_Bbox1 Action Formula (infix "\<unrhd>\<^sub>1" 330)
                 | Formula_Bdiam2 Agent Formula (infix "\<triangleq>\<^sub>2" 330)
                 | Formula_Bbox2 Agent Formula (infix "\<unrhd>\<^sub>2" 330)


(* Structural level *)

datatype Formula_S = Formula_Atomic_S Formula ("_ \<^sub>S\<^sub>F\<^sub>M" [330] 340)
                   | Formula_Neutral_S ("I\<^sub>S")
                   | Formula_Comma_S Formula_S Formula_S (infix ";\<^sub>S" 340)
                   | Formula_Bigcomma_S "Formula_S list" (";;\<^sub>S _" [330] 331)
                   | Formula_ImpR_S Formula_S Formula_S (infix "\<rightarrow>\<^sub>S" 340)
                   | Formula_ImpL_S Formula_S Formula_S (infix "\<leftarrow>\<^sub>S" 340)

                   | Formula_Fdiam0_S Funaction_S Formula_S (infix "\<triangle>\<^sub>0\<^sub>S" 340)
                   | Formula_Fbox0_S Funaction_S Formula_S (infix "\<rhd>\<^sub>0\<^sub>S" 340)
                   | Formula_Fdiam1_S Action_S Formula_S (infix "\<triangle>\<^sub>1\<^sub>S" 340)
                   | Formula_Fbox1_S Action_S Formula_S (infix "\<rhd>\<^sub>1\<^sub>S" 340)
                   | Formula_Fdiam2_S Agent_S Formula_S (infix "\<triangle>\<^sub>2\<^sub>S" 340)
                   | Formula_Fbox2_S Agent_S Formula_S (infix "\<rhd>\<^sub>2\<^sub>S" 340)

                   | Formula_Bdiam0_S Funaction_S Formula_S (infix "\<triangleq>\<^sub>0\<^sub>S" 340)
                   | Formula_Bbox0_S Funaction_S  Formula_S (infix "\<unrhd>\<^sub>0\<^sub>S" 340)
                   | Formula_Bdiam1_S Action_S Formula_S (infix "\<triangleq>\<^sub>1\<^sub>S" 340)
                   | Formula_Bbox1_S Action_S Formula_S (infix "\<unrhd>\<^sub>1\<^sub>S" 340)
                   | Formula_Bdiam2_S Agent_S Formula_S (infix "\<triangleq>\<^sub>2\<^sub>S" 340)
                   | Formula_Bbox2_S Agent_S Formula_S (infix "\<unrhd>\<^sub>2\<^sub>S" 340)

and Funaction_S =    Funaction_Atomic_S Funaction ("_ \<^sub>S\<^sub>F\<^sub>A" [330] 340)
                   | Funaction_wlas0_S Formula_S Formula_S (infix "\<lhd>~\<^sub>0\<^sub>S" 340)
                   | Funaction_blas0_S Formula_S Formula_S (infix "\<unlhd>~\<^sub>0\<^sub>S" 340)
                   | Function_wras3_S Agent_S Action_S (infix "~\<rhd>\<^sub>3\<^sub>S" 340)
                   | Function_bras3_S Agent_S Action_S (infix "~\<unrhd>\<^sub>3\<^sub>S" 340)

and Action_S =       Action_Atomic_S Action ("_ \<^sub>S\<^sub>A\<^sub>C" [330] 340)
                   | Action_Bdiam3_S Agent_S Funaction_S (infix "\<triangleq>\<^sub>3\<^sub>S" 340)
                   | Action_Fdiam3_S Agent_S Funaction_S (infix "\<triangle>\<^sub>3\<^sub>S" 340)
                   | Action_wla1_S Formula_S Formula_S (infix "\<lhd>\<^sub>1\<^sub>S" 340)
                   | Action_bla1_S Formula_S Formula_S (infix "\<unlhd>\<^sub>1\<^sub>S" 340)
                                                                     
and Agent_S =        Agent_Atomic_S Agent ("_ \<^sub>S\<^sub>A\<^sub>G" [330] 340)
                   | Agent_wlas2_S Formula_S Formula_S (infix "\<lhd>~\<^sub>2\<^sub>S" 340)
                   | Agent_blas2_S Formula_S Formula_S (infix "\<unlhd>~\<^sub>2\<^sub>S" 340)
                   | Agent_wlas3_S Action_S Funaction_S (infix "\<lhd>~\<^sub>3\<^sub>S" 340)
                   | Agent_blas3_S Action_S Funaction_S (infix "\<unlhd>~\<^sub>3\<^sub>S" 340)


(* Sequents *)

datatype Sequent =   Sequent_Formula Formula_S Formula_S ("_ \<turnstile>\<^sub>F\<^sub>M _" [311,311] 310)
                   | Sequent_Funaction Funaction_S Funaction_S ("_ \<turnstile>\<^sub>F\<^sub>A _" [311,311] 310)
                   | Sequent_Action Action_S Action_S ("_ \<turnstile>\<^sub>A\<^sub>C _" [311,311] 310)
                   | Sequent_Agent Agent_S Agent_S ("_ \<turnstile>\<^sub>A\<^sub>G _" [311,311] 310)


end