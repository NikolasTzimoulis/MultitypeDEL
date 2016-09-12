theory MDEAK_examples_completeness
imports Main MDEAK_Core_SE MDEAK_SE MDEAK_examples
begin

lemma c1_f: "\<turnstile>d (a \<triangle>\<^sub>2 ((p)\<^sub>F) )\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M ((a \<triangle>\<^sub>2 \<top>) \<and>\<^sub>F ((p)\<^sub>F))\<^sub>S\<^sub>F\<^sub>M"
sledgehammer [timeout=120, fact_thresholds=0.1 0.7]
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
sledgehammer [isar_proofs=true, compress=3]
proof -
  have f1: "\<forall>f fa. \<not> \<turnstile>d f \<turnstile>\<^sub>F\<^sub>M I\<^sub>S \<or> \<turnstile>d f \<turnstile>\<^sub>F\<^sub>M fa"
    by (metis IW_R)
  have f2: "\<forall>f fa fb. \<not> \<turnstile>d f \<turnstile>\<^sub>F\<^sub>M fa \<rightarrow>\<^sub>S fb \<or> \<turnstile>d fa ;\<^sub>S f \<turnstile>\<^sub>F\<^sub>M fb"
    by (metis D_IR1_b)
  have f3: "\<forall>f fa fb. \<not> \<turnstile>d f ;\<^sub>S fa \<turnstile>\<^sub>F\<^sub>M fb \<or> \<turnstile>d fa ;\<^sub>S f \<turnstile>\<^sub>F\<^sub>M fb"
    by (metis E_L)
  have f4: "\<forall>f fa fb. \<not> \<turnstile>d f ;\<^sub>S fa \<turnstile>\<^sub>F\<^sub>M fb \<or> \<turnstile>d fa \<turnstile>\<^sub>F\<^sub>M f \<rightarrow>\<^sub>S fb"
    by (metis D_IR1_f)
  have "\<turnstile>d (a \<rhd>\<^sub>2 \<bottom>) \<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M a \<^sub>S\<^sub>A\<^sub>G \<rhd>\<^sub>2\<^sub>S I\<^sub>S"
    by (meson Bot_L Fbox2_L Id_ag)
  then have "\<turnstile>d a \<^sub>S\<^sub>A\<^sub>G \<triangleq>\<^sub>2\<^sub>S (a \<rhd>\<^sub>2 \<bottom>) \<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M I\<^sub>S"
    by (metis DH_bdiam2_b)
  then have "\<turnstile>d \<top> \<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M a \<^sub>S\<^sub>A\<^sub>G \<unrhd>\<^sub>2\<^sub>S ((a \<rhd>\<^sub>2 \<bottom>) \<^sub>S\<^sub>F\<^sub>M \<rightarrow>\<^sub>S \<bottom> \<^sub>S\<^sub>F\<^sub>M)"
    using f4 f3 f2 f1 by (meson FS_bbox2)
  then have "\<turnstile>d a \<^sub>S\<^sub>A\<^sub>G \<triangle>\<^sub>2\<^sub>S \<top> \<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M (a \<rhd>\<^sub>2 \<bottom>) \<^sub>S\<^sub>F\<^sub>M \<rightarrow>\<^sub>S \<bottom> \<^sub>S\<^sub>F\<^sub>M"
    by (metis DH_fdiam2_b)
  then have "\<turnstile>d (a \<triangle>\<^sub>2 \<top>) \<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M (a \<rhd>\<^sub>2 \<bottom>) \<^sub>S\<^sub>F\<^sub>M \<rightarrow>\<^sub>S \<bottom> \<^sub>S\<^sub>F\<^sub>M"
    by (metis Fdiam2_L)
  then have "\<turnstile>d (a \<rhd>\<^sub>2 \<bottom>) \<^sub>S\<^sub>F\<^sub>M ;\<^sub>S (a \<triangle>\<^sub>2 \<top>) \<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M \<bottom> \<^sub>S\<^sub>F\<^sub>M"
    using f2 by metis
  then have "\<turnstile>d (a \<triangle>\<^sub>2 \<top>) \<^sub>S\<^sub>F\<^sub>M ;\<^sub>S (a \<rhd>\<^sub>2 \<bottom>) \<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M \<bottom> \<^sub>S\<^sub>F\<^sub>M"
    using f3 by meson
  then have "\<turnstile>d (a \<rhd>\<^sub>2 \<bottom>) \<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M (a \<triangle>\<^sub>2 \<top>) \<^sub>S\<^sub>F\<^sub>M \<rightarrow>\<^sub>S \<bottom> \<^sub>S\<^sub>F\<^sub>M"
    using f4 by metis
  then show ?thesis
    by (metis ImpR_R)
qed
(*by (meson Bot_L DH_bdiam2_b DH_fdiam2_b D_IR1_b D_IR1_f E_L FS_bbox2 Fbox2_L Fdiam2_L IW_R Id_ag ImpR_R)*)

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