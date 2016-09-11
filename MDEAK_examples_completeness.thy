theory MDEAK_examples_completeness
imports Main MDEAK_Core_SE MDEAK_SE MDEAK_examples
begin

lemma c1_f: "\<turnstile>d (a \<triangle>\<^sub>2 ((p)\<^sub>F) )\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M ((a \<triangle>\<^sub>2 \<top>) \<and>\<^sub>F ((p)\<^sub>F))\<^sub>S\<^sub>F\<^sub>M"
(*sledgehammer*)
sorry

lemma c1_b: "\<turnstile>d ((a \<triangle>\<^sub>2 \<top>) \<and>\<^sub>F (p)\<^sub>F)\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M (a \<triangle>\<^sub>2 (p)\<^sub>F)\<^sub>S\<^sub>F\<^sub>M"
(*sledgehammer*)
sorry

lemma c2_f: "\<turnstile>d (a \<rhd>\<^sub>2 (p)\<^sub>F)\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M ((a \<triangle>\<^sub>2 \<top>) \<rightarrow>\<^sub>F (p)\<^sub>F)\<^sub>S\<^sub>F\<^sub>M"
(*sledgehammer*)
sorry

lemma c2_b: "\<turnstile>d ((a \<triangle>\<^sub>2 \<top>) \<rightarrow>\<^sub>F (p)\<^sub>F)\<^sub>S\<^sub>F\<^sub>M  \<turnstile>\<^sub>F\<^sub>M (a \<rhd>\<^sub>2 (p)\<^sub>F)\<^sub>S\<^sub>F\<^sub>M"
(*sledgehammer*)
sorry

lemma c3: "\<turnstile>d (a \<triangle>\<^sub>2 \<top>)\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M (a \<triangle>\<^sub>2 \<top>)\<^sub>S\<^sub>F\<^sub>M"
(*sledgehammer*)
using [[simp_trace_new mode=full]] 
by (simp add: Fdiam2_L Fdiam2_R Id_ag Top_L Top_R)

lemma c4_f: "\<turnstile>d (a \<rhd>\<^sub>2 \<bottom>)\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M ((a \<triangle>\<^sub>2 \<top>) \<rightarrow>\<^sub>F \<bottom>)\<^sub>S\<^sub>F\<^sub>M"
(*sledgehammer*)
by (meson Bot_L DH_bdiam2_b DH_fdiam2_b D_IR1_b D_IR1_f E_L FS_bbox2 Fbox2_L Fdiam2_L IW_R Id_ag ImpR_R)

lemma c4_b: "\<turnstile>d ((a \<triangle>\<^sub>2 \<top>) \<rightarrow>\<^sub>F \<bottom>)\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M (a \<rhd>\<^sub>2 \<bottom>)\<^sub>S\<^sub>F\<^sub>M"
(*sledgehammer*)
sorry

lemma c5_f: "\<turnstile>d (a \<triangle>\<^sub>2 \<bottom>)\<^sub>S\<^sub>F\<^sub>M  \<turnstile>\<^sub>F\<^sub>M (\<bottom>)\<^sub>S\<^sub>F\<^sub>M"
(*sledgehammer*)
using Bot_L DH_fdiam2_b Fdiam2_L IW_R by blast

lemma c5_b: "\<turnstile>d (\<bottom>)\<^sub>S\<^sub>F\<^sub>M  \<turnstile>\<^sub>F\<^sub>M (a \<triangle>\<^sub>2 \<bottom>)\<^sub>S\<^sub>F\<^sub>M"
(*sledgehammer*)
using [[simp_trace_new mode=full]] 
by (simp add: Bot_L IW_R)

lemma c6_f: "\<turnstile>d (a \<rhd>\<^sub>2 \<top>)\<^sub>S\<^sub>F\<^sub>M  \<turnstile>\<^sub>F\<^sub>M (\<top>)\<^sub>S\<^sub>F\<^sub>M"
(*sledgehammer*)
using [[simp_trace_new mode=full]] 
by (simp add: IW_L Top_R)

lemma c6_b: "\<turnstile>d (\<top>)\<^sub>S\<^sub>F\<^sub>M  \<turnstile>\<^sub>F\<^sub>M (a \<rhd>\<^sub>2 \<top>)\<^sub>S\<^sub>F\<^sub>M"
(*sledgehammer*)
using [[simp_trace_new mode=full]] 
by (simp add: DH_bdiam2_f Fbox2_R IW_L Top_R)

lemma c7_f: "\<turnstile>d (a \<rhd>\<^sub>2 (A \<and>\<^sub>F B))\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M ((a \<rhd>\<^sub>2 A) \<and>\<^sub>F (a \<rhd>\<^sub>2 B))\<^sub>S\<^sub>F\<^sub>M"
(*sledgehammer*)
sorry

lemma c7_b: "\<turnstile>d ((a \<rhd>\<^sub>2 A) \<and>\<^sub>F (a \<rhd>\<^sub>2 B))\<^sub>S\<^sub>F\<^sub>M  \<turnstile>\<^sub>F\<^sub>M (a \<rhd>\<^sub>2 (A \<and>\<^sub>F B))\<^sub>S\<^sub>F\<^sub>M"
(*sledgehammer*)
sorry

lemma c8_f: "\<turnstile>d (a \<triangle>\<^sub>2 (A \<and>\<^sub>F B))\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M ((a \<triangle>\<^sub>2 A) \<and>\<^sub>F (a \<triangle>\<^sub>2 B))\<^sub>S\<^sub>F\<^sub>M"
(*sledgehammer*)
by (metis And_L And_R C_L D_IL1_b D_IR1_b Fdiam2_L Fdiam2_R Id_ag W_1L W_2L AderivesA)

lemma c8_b: "\<turnstile>d ((a \<triangle>\<^sub>2 A) \<and>\<^sub>F (a \<triangle>\<^sub>2 B))\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M (a \<triangle>\<^sub>2 (A \<and>\<^sub>F B))\<^sub>S\<^sub>F\<^sub>M"
(*sledgehammer*)
sorry

lemma c8_f_simple: "\<turnstile>d (a \<triangle>\<^sub>2 ((A)\<^sub>F \<and>\<^sub>F (B)\<^sub>F))\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M ((a \<triangle>\<^sub>2 (A)\<^sub>F) \<and>\<^sub>F (a \<triangle>\<^sub>2 (B)\<^sub>F) )\<^sub>S\<^sub>F\<^sub>M"
(*sledgehammer*)
by (metis And_L And_R C_L D_IL1_b D_IR1_b Fdiam2_L Fdiam2_R Id_ag Id_fm W_1L W_2L)

lemma c8_b_simple: "\<turnstile>d ((a \<triangle>\<^sub>2 (A)\<^sub>F) \<and>\<^sub>F (a \<triangle>\<^sub>2 (B)\<^sub>F) )\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M (a \<triangle>\<^sub>2 ((A)\<^sub>F \<and>\<^sub>F (B)\<^sub>F))\<^sub>S\<^sub>F\<^sub>M"
(*sledgehammer*)
sorry