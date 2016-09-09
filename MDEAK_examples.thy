theory MDEAK_examples
imports Main MDEAK_Core_SE MDEAK_SE MDEAK_method
begin

lemma l1: "\<turnstile>d (A\<^sub>F)\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M (A\<^sub>F)\<^sub>S\<^sub>F\<^sub>M"
(*by (rule Id_fm)   *)
using [[simp_trace_new mode=full]] 
by mdeak

lemma l2: "\<turnstile>d Y \<turnstile>\<^sub>F\<^sub>M ((A \<^sub>F) \<^sub>S\<^sub>F\<^sub>M)  \<rightarrow>\<^sub>S ((A \<^sub>F) \<^sub>S\<^sub>F\<^sub>M)"
using [[simp_trace_new mode=full]] 
(*by mdeak*)
by (simp only: W_2L l1)
(*by (simp only: derivable.intros)
by (simp only: derivable.simps)
by (simp only: derivable.cases)
by (simp only: derivable.induct)*)
(*by (simp only: IW_L I_2L_f Id_fm )*)
(*apply (rule IW_L)
apply (rule I_2L_f)
apply (rule Id)
done*)

lemma l3: "\<turnstile>d Y \<turnstile>\<^sub>F\<^sub>M ((A \<^sub>F) \<rightarrow>\<^sub>F (A \<^sub>F))\<^sub>S\<^sub>F\<^sub>M"
using [[simp_trace_new mode=full]] 
apply(rule ImpR_R)
apply(rule l2)
done
(*using Bot_L IW_L I_2L_f ImpR_R by blast*)

(* Completeness theorems *)

lemma c1_f: "\<turnstile>d (a \<triangle>\<^sub>2 p\<^sub>F)\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M ((a \<triangle>\<^sub>2 \<top>) \<and>\<^sub>F p\<^sub>F)\<^sub>S\<^sub>F\<^sub>M"
(*sledgehammer*)
using DH_blas2_f Fdiam2_L Id_ag by blast
(*by mdeak*)
(*by mdeak_b*)
(*by (simp only: DH_blas2_f Fdiam2_L Id_ag) *)

lemma c1_b: "\<turnstile>d ((a \<triangle>\<^sub>2 \<top>) \<and>\<^sub>F p\<^sub>F)\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M (a \<triangle>\<^sub>2 p\<^sub>F)\<^sub>S\<^sub>F\<^sub>M"
(*sledgehammer*)
using And_L Bot_L D_IR1_b IW_R by blast
(*by (simp add: And_L Bot_L D_IR1_b IW_R)*)


lemma c2_f: "\<turnstile>d (a \<rhd>\<^sub>2 p)\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M ((a \<triangle>\<^sub>2 \<top>) \<rightarrow>\<^sub>F p)\<^sub>S\<^sub>F\<^sub>M"
(*sledgehammer*)
using IW_L I_2L_f ImpR_R Top_R by blast
(*by (simp add: IW_L I_2L_f ImpR_R Top_R)*)
(*using ImpR_R l2 by blast*)

lemma c2_b: "\<turnstile>d ((a \<triangle>\<^sub>2 \<top>) \<rightarrow>\<^sub>F p)\<^sub>S\<^sub>F\<^sub>M  \<turnstile>\<^sub>F\<^sub>M (a \<rhd>\<^sub>2 p)\<^sub>S\<^sub>F\<^sub>M"
(*sledgehammer*)
(*using DH_bdiam2_f Fbox2_R l2 by blast*)
by (blast intro: DH_bdiam2_f Fbox2_R l2)

lemma c3_f: "\<turnstile>d (a \<triangle>\<^sub>2 (A\<^sub>F \<and>\<^sub>F B\<^sub>F))\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M ((a \<triangle>\<^sub>2 A\<^sub>F) \<and>\<^sub>F (a \<triangle>\<^sub>2 B\<^sub>F) )\<^sub>S\<^sub>F\<^sub>M"
(*sledgehammer*)
using And_R C_L IW_L Top_R by blast
(*using Bot_L DH_fdiam2_b Fdiam2_L IW_R by blast*)
(*using DH_blas2_f Fdiam2_L Id_ag by blast*)

lemma c3_b: "\<turnstile>d ((a \<triangle>\<^sub>2 A\<^sub>F) \<and>\<^sub>F (a \<triangle>\<^sub>2 B\<^sub>F) )\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M (a \<triangle>\<^sub>2 (A\<^sub>F \<and>\<^sub>F B\<^sub>F))\<^sub>S\<^sub>F\<^sub>M "
using And_L Bot_L D_IL1_b IW_R by blast

end                    

