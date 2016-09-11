theory MDEAK_examples
imports Main MDEAK_Core_SE MDEAK_SE MDEAK_method
begin

lemma l1: "\<turnstile>d (A \<^sub>F)\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M (A \<^sub>F)\<^sub>S\<^sub>F\<^sub>M"
(*by (rule Id_fm)   *)
using [[simp_trace_new mode=full]] 
by mdeak

lemma l2: "\<turnstile>d Y \<turnstile>\<^sub>F\<^sub>M ((A \<^sub>F) \<^sub>S\<^sub>F\<^sub>M) \<rightarrow>\<^sub>S ((A \<^sub>F) \<^sub>S\<^sub>F\<^sub>M)"
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

lemma step1 : "\<turnstile>d (a)\<^sub>S\<^sub>A\<^sub>C \<turnstile>\<^sub>A\<^sub>C (a)\<^sub>S\<^sub>A\<^sub>C"
(*sledgehammer*)
by (metis Action.exhaust Bdiam3_L Bdiam3_R Fdiam3_L Fdiam3_R Id_ag Id_fa)

theorem AderivesA : "\<turnstile>d (A)\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M (A)\<^sub>S\<^sub>F\<^sub>M"
apply(induction A)
apply (simp add: l1)
apply (simp add: Top_L Top_R)
apply (simp add: Bot_L Bot_R)
apply (simp add: And_L And_R)
apply (simp add: Or_L Or_R)
apply (simp add: ImpR_L ImpR_R)
apply (simp add: ImpL_L ImpL_R)
apply (simp add: DimpR_L DimpR_R)
apply (simp add: DimpL_L DimpL_R)
apply (simp add: Fdiam0_L Fdiam0_R Id_fa)
apply (simp add: Fbox0_L Fbox0_R Id_fa)
apply (simp add: Fdiam1_L Fdiam1_R step1)
apply (simp add: Fbox1_L Fbox1_R step1)
apply (simp add: Fdiam2_L Fdiam2_R Id_ag)
apply (simp add: Fbox2_L Fbox2_R Id_ag)
apply (simp add: Bdiam0_L Bdiam0_R Id_fa)
apply (simp add: Bbox0_L Bbox0_R Id_fa)
apply (simp add: Bdiam1_L Bdiam1_R step1)
apply (simp add: Bbox1_L Bbox1_R step1)
apply (simp add: Bdiam2_L Bdiam2_R Id_ag)
by (simp add: Bbox2_L Bbox2_R Id_ag)
end                    

