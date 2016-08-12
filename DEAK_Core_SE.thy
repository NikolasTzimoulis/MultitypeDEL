theory (*calc_name_core_se-BEGIN*)DEAK_Core_SE(*calc_name_core_se-END*)
imports Main
begin

(*calc_structure_se-BEGIN*)
type_synonym Action = string

type_synonym Agent = string

type_synonym Atprop = string

type_synonym funaction = string

datatype Formula = Formula_FboxA Action Formula ("fboxA\<^sub>F _ _" [330,330] 331)
                 | Formula_FdiamA Action Formula ("fdiamA\<^sub>F _ _" [330,330] 331)
                 | Formula_BboxA Action Formula ("bboxA\<^sub>F _ _" [330,330] 331)
                 | Formula_BdiamA Action Formula ("bdiamA\<^sub>F _ _" [330,330] 331)
                 | Formula_FboxK Agent Formula ("fboxK\<^sub>F _ _" [330,330] 331)
                 | Formula_FdiamK Agent Formula ("fdiamK\<^sub>F _ _" [330,330] 331)
                 | Formula_BboxK Agent Formula ("bboxK\<^sub>F _ _" [330,330] 331)
                 | Formula_BdiamK Agent Formula ("bdiamK\<^sub>F _ _" [330,330] 331)
                 | Formula_Atprop Atprop ("_ \<^sub>F" [320] 330)
                 | Formula_And Formula Formula (infix "\<and>\<^sub>F" 330)
                 | Formula_ImpL Formula Formula (infix "\<leftarrow>\<^sub>F" 330)
                 | Formula_DImpL Formula Formula (infix "-<\<^sub>F" 330)
                 | Formula_DImpR Formula Formula (infix ">-\<^sub>F" 330)
                 | Formula_Or Formula Formula (infix "\<or>\<^sub>F" 330)
                 | Formula_ImpR Formula Formula (infix "\<rightarrow>\<^sub>F" 330)
                 | Formula_Precondition Action ("One\<^sub>F _" [340] 330)
                 | Formula_Top ("\<top>\<^sub>F")
                 | Formula_Bot ("\<bottom>\<^sub>F")

datatype Structure = Structure_w0triangle Structure_f Structure (infix "\<triangle>\<^sub>0" 340)
                   | Structure_b0triangle Structure_f Structure (infix "\<triangleq>\<^sub>0" 340)
                   | Structure_w0rarrow Structure_f Structure (infix "\<rhd>\<^sub>0" 340)
                   | Structure_b0rarrow Structure_f Structure (infix "\<unrhd>\<^sub>0" 340)

                   | Structure_w1triangle Structure_a Structure (infix "\<triangle>\<^sub>1" 340)
                   | Structure_b1triangle Structure_a Structure (infix "\<triangleq>\<^sub>1" 340)
                   | Structure_w1rarrow Structure_a Structure (infix "\<rhd>\<^sub>1" 340)
                   | Structure_b1rarrow Structure_a Structure (infix "\<unrhd>\<^sub>1" 340)

                   | Structure_w2triangle Structure_A Structure (infix "\<triangle>\<^sub>2" 340)
                   | Structure_b2triangle Structure_A Structure (infix "\<triangleq>\<^sub>2" 340)
                   | Structure_w2rarrow Structure_A Structure (infix "\<rhd>\<^sub>2" 340)
                   | Structure_b2rarrow Structure_A Structure (infix "\<unrhd>\<^sub>2" 340)

                   | Structure_BackA Action Structure ("backA\<^sub>S _ _" [330,330] 331)
                   | Structure_BackK Agent Structure ("backK\<^sub>S _ _" [330,330] 331)
                   | Structure_ForwK Agent Structure ("forwK\<^sub>S _ _" [330,330] 331)
                   | Structure_Bigcomma "Structure list" (";;\<^sub>S _" [330] 331)
                   | Structure_Comma Structure Structure (infix ";\<^sub>S" 340)
                   | Structure_ImpL Structure Structure (infix "\<leftarrow>\<^sub>S" 340)
                   | Structure_ImpR Structure Structure (infix "\<rightarrow>\<^sub>S" 340)
                   | Structure_Formula Formula ("_ \<^sub>S" [330] 340)
                   | Structure_Phi Action ("Phi\<^sub>S _" [340] 330)
                   | Structure_Neutral ("I\<^sub>S")

datatype Structure_f = Structure_funaction funaction ("_ \<^sub>f" [330] 340)
                   |   Structure_w0lsquiglyarrow Structure Structure (infix "\<lhd>~\<^sub>0" 340)
                   |   Structure_b0lsquiglyarrow Structure Structure (infix "\<unlhd>~\<^sub>0" 340)
                   |   Structure_w3rsquiglyarrow Structure_A Structure_a (infix "~\<rhd>\<^sub>3" 340)
                   |   Structure_b3rsquiglyarrow Structure_A Structure_a (infix "~\<unrhd>\<^sub>3" 340)

datatype Structure_A = Structure_Agent Agent ("_ \<^sub>A" [330] 340)
                   |   Structure_w2lsquiglyarrow Structure Structure (infix "\<lhd>~\<^sub>2" 340)
                   |   Structure_b2lsquiglyarrow Structure Structure (infix "\<unlhd>~\<^sub>2" 340)
                   |   Structure_w3lsquiglyarrow Structure_a Structure_f (infix "\<lhd>~\<^sub>3" 340)
                   |   Structure_b3lsquiglyarrow Structure_a Structure_f (infix "\<unlhd>~\<^sub>3" 340)

datatype Structure_a = Structure_b3triangle Structure_A Structure_f (infix "\<triangleq>\<^sub>3" 340)
                   |   Structure_w3triangle Structure_A Structure_f (infix "\<triangle>\<^sub>3" 340)
                   |   Structure_w1larrow Structure Structure (infix "\<lhd>\<^sub>1" 340)
                   |   Structure_b1larrow Structure Structure (infix "\<unlhd>\<^sub>1" 340)

datatype Sequent = Sequent Structure Structure ("_ \<turnstile>\<^sub>S _" [311,311] 310)
datatype Sequent_Agent = Sequent_Agent Structure_A Structure_A ("_ \<turnstile>\<^sub>A _" [311,311] 310)
datatype Sequent_action = Sequent_action Structure_a Structure_a ("_ \<turnstile>\<^sub>a _" [311,311] 310)
datatype Sequent_function = Sequent_function Structure_f Structure_f ("_ \<turnstile>\<^sub>f _" [311,311] 310)
(*calc_structure_se-END*)


end