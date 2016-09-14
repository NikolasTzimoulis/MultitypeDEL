theory MDEAK_examples_completeness
imports Main MDEAK_Core_SE MDEAK_SE MDEAK_examples
begin

lemma c1_f: "\<turnstile>d (a \<triangle>\<^sub>0 ((p)\<^sub>F) )\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M ((a \<triangle>\<^sub>0 \<top>) \<and>\<^sub>F ((p)\<^sub>F))\<^sub>S\<^sub>F\<^sub>M"
proof - 
  have "\<turnstile>d (a)\<^sub>S\<^sub>F\<^sub>A \<triangle>\<^sub>0\<^sub>S ((p)\<^sub>F)\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M ((p)\<^sub>F)\<^sub>S\<^sub>F\<^sub>M"
    by (simp add: Atom)
  then have "\<turnstile>d (a)\<^sub>S\<^sub>F\<^sub>A \<triangle>\<^sub>0\<^sub>S I\<^sub>S \<turnstile>\<^sub>F\<^sub>M (a \<triangle>\<^sub>0 \<top>)\<^sub>S\<^sub>F\<^sub>M"
    by (simp add: Fdiam0_R Id_fa Top_R)
  then have "\<turnstile>d (a)\<^sub>S\<^sub>F\<^sub>A \<triangle>\<^sub>0\<^sub>S (I\<^sub>S ;\<^sub>S ((p)\<^sub>F)\<^sub>S\<^sub>F\<^sub>M) \<turnstile>\<^sub>F\<^sub>M ((a \<triangle>\<^sub>0 \<top>) \<and>\<^sub>F ((p)\<^sub>F))\<^sub>S\<^sub>F\<^sub>M"
    by (simp add: And_R Mon_fdiam0 \<open>\<turnstile>d a \<^sub>S\<^sub>F\<^sub>A \<triangle>\<^sub>0\<^sub>S p \<^sub>F \<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M p \<^sub>F \<^sub>S\<^sub>F\<^sub>M\<close>)
  then have "\<turnstile>d ((p)\<^sub>F)\<^sub>S\<^sub>F\<^sub>M  \<turnstile>\<^sub>F\<^sub>M (a)\<^sub>S\<^sub>F\<^sub>A \<unrhd>\<^sub>0\<^sub>S ((a \<triangle>\<^sub>0 \<top>) \<and>\<^sub>F ((p)\<^sub>F))\<^sub>S\<^sub>F\<^sub>M"
    using DH_fdiam0_f D_IL1_f I_1L_b by blast
  then show ?thesis
    by (simp add: DH_fdiam0_b Fdiam0_L)
qed

lemma c1_b: "\<turnstile>d ((a \<triangle>\<^sub>0 \<top>) \<and>\<^sub>F (p)\<^sub>F)\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M (a \<triangle>\<^sub>0 (p)\<^sub>F)\<^sub>S\<^sub>F\<^sub>M"
proof - 
  have "\<turnstile>d (a)\<^sub>S\<^sub>F\<^sub>A \<triangle>\<^sub>0\<^sub>S (((a)\<^sub>S\<^sub>F\<^sub>A \<triangleq>\<^sub>0\<^sub>S ((p)\<^sub>F)\<^sub>S\<^sub>F\<^sub>M) ;\<^sub>S (\<top>)\<^sub>S\<^sub>F\<^sub>M ) \<turnstile>\<^sub>F\<^sub>M (a \<triangle>\<^sub>0 (p)\<^sub>F)\<^sub>S\<^sub>F\<^sub>M"
    by (simp add: Atom D_IR1_b Fdiam0_R Id_fa W_2L)
  then show ?thesis
    using And_L Conj_fdiam0 D_IR1_b D_IR1_f E_L Fdiam0_L by blast
qed

lemma c2_f: "\<turnstile>d (a \<rhd>\<^sub>0 (p)\<^sub>F)\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M ((a \<triangle>\<^sub>0 \<top>) \<rightarrow>\<^sub>F (p)\<^sub>F)\<^sub>S\<^sub>F\<^sub>M"
proof - 
  have "\<turnstile>d (a)\<^sub>S\<^sub>F\<^sub>A \<triangleq>\<^sub>0\<^sub>S (a \<rhd>\<^sub>0 (p)\<^sub>F)\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M (a)\<^sub>S\<^sub>F\<^sub>A \<unrhd>\<^sub>0\<^sub>S ((p)\<^sub>F)\<^sub>S\<^sub>F\<^sub>M"
    by (simp add: Atom DH_bdiam0_b Fbox0_L Id_fa)
  then show ?thesis
    by (simp add: DH_fdiam0_b D_IR1_b D_IR1_f E_L FS_bbox0 Fdiam0_L ImpR_R W_2L)
qed

lemma c2_b: "\<turnstile>d ((a \<triangle>\<^sub>0 \<top>) \<rightarrow>\<^sub>F (p)\<^sub>F)\<^sub>S\<^sub>F\<^sub>M  \<turnstile>\<^sub>F\<^sub>M (a \<rhd>\<^sub>0 (p)\<^sub>F)\<^sub>S\<^sub>F\<^sub>M"
sledgehammer
proof - 
  have "\<turnstile>d ((a \<triangle>\<^sub>0 \<top>) \<rightarrow>\<^sub>F (p)\<^sub>F)\<^sub>S\<^sub>F\<^sub>M  \<turnstile>\<^sub>F\<^sub>M (a)\<^sub>S\<^sub>F\<^sub>A \<rhd>\<^sub>0\<^sub>S (I\<^sub>S \<rightarrow>\<^sub>S ((p)\<^sub>F)\<^sub>S\<^sub>F\<^sub>M)"
    by (simp add: Atom FS_fbox0 Fdiam0_R Id_fa ImpR_L Top_R)
  then show ?thesis
    using DH_bdiam0_b DH_bdiam0_f D_IL1_f D_IR1_b Fbox0_R I_1L_b by blast
qed

lemma c3: "\<turnstile>d (a \<triangle>\<^sub>0 \<top>)\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M (a \<triangle>\<^sub>0 \<top>)\<^sub>S\<^sub>F\<^sub>M"
by (simp add: AderivesA)

lemma c4_f: "\<turnstile>d (a \<rhd>\<^sub>0 \<bottom>)\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M ((a \<triangle>\<^sub>0 \<top>) \<rightarrow>\<^sub>F \<bottom>)\<^sub>S\<^sub>F\<^sub>M"
proof -
  have f1: "\<forall>f fa. \<not> \<turnstile>d f \<turnstile>\<^sub>F\<^sub>M I\<^sub>S \<or> \<turnstile>d f \<turnstile>\<^sub>F\<^sub>M fa"
    by (metis IW_R)
  have f2: "\<forall>f fa fb. \<not> \<turnstile>d f \<turnstile>\<^sub>F\<^sub>M fa \<rightarrow>\<^sub>S fb \<or> \<turnstile>d fa ;\<^sub>S f \<turnstile>\<^sub>F\<^sub>M fb"
    by (metis D_IR1_b)
  have f3: "\<forall>f fa fb. \<not> \<turnstile>d f ;\<^sub>S fa \<turnstile>\<^sub>F\<^sub>M fb \<or> \<turnstile>d fa ;\<^sub>S f \<turnstile>\<^sub>F\<^sub>M fb"
    by (metis E_L)
  have f4: "\<forall>f fa fb. \<not> \<turnstile>d f ;\<^sub>S fa \<turnstile>\<^sub>F\<^sub>M fb \<or> \<turnstile>d fa \<turnstile>\<^sub>F\<^sub>M f \<rightarrow>\<^sub>S fb"
    by (metis D_IR1_f)
  have "\<turnstile>d (a \<rhd>\<^sub>0 \<bottom>) \<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M a \<^sub>S\<^sub>F\<^sub>A \<rhd>\<^sub>0\<^sub>S I\<^sub>S"
    by (meson Bot_L Fbox0_L Id_fa)
  then have "\<turnstile>d a \<^sub>S\<^sub>F\<^sub>A \<triangleq>\<^sub>0\<^sub>S (a \<rhd>\<^sub>0 \<bottom>) \<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M I\<^sub>S"
    by (metis DH_bdiam0_b)
  then have "\<turnstile>d \<top> \<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M a \<^sub>S\<^sub>F\<^sub>A \<unrhd>\<^sub>0\<^sub>S ((a \<rhd>\<^sub>0 \<bottom>) \<^sub>S\<^sub>F\<^sub>M \<rightarrow>\<^sub>S \<bottom> \<^sub>S\<^sub>F\<^sub>M)"
    using f4 f3 f2 f1 by (meson FS_bbox0)
  then have "\<turnstile>d a \<^sub>S\<^sub>F\<^sub>A \<triangle>\<^sub>0\<^sub>S \<top> \<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M (a \<rhd>\<^sub>0 \<bottom>) \<^sub>S\<^sub>F\<^sub>M \<rightarrow>\<^sub>S \<bottom> \<^sub>S\<^sub>F\<^sub>M"
    by (metis DH_fdiam0_b)
  then have "\<turnstile>d (a \<triangle>\<^sub>0 \<top>) \<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M (a \<rhd>\<^sub>0 \<bottom>) \<^sub>S\<^sub>F\<^sub>M \<rightarrow>\<^sub>S \<bottom> \<^sub>S\<^sub>F\<^sub>M"
    by (metis Fdiam0_L)
  then have "\<turnstile>d (a \<rhd>\<^sub>0 \<bottom>) \<^sub>S\<^sub>F\<^sub>M ;\<^sub>S (a \<triangle>\<^sub>0 \<top>) \<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M \<bottom> \<^sub>S\<^sub>F\<^sub>M"
    using f2 by metis
  then have "\<turnstile>d (a \<triangle>\<^sub>0 \<top>) \<^sub>S\<^sub>F\<^sub>M ;\<^sub>S (a \<rhd>\<^sub>0 \<bottom>) \<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M \<bottom> \<^sub>S\<^sub>F\<^sub>M"
    using f3 by meson
  then have "\<turnstile>d (a \<rhd>\<^sub>0 \<bottom>) \<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M (a \<triangle>\<^sub>0 \<top>) \<^sub>S\<^sub>F\<^sub>M \<rightarrow>\<^sub>S \<bottom> \<^sub>S\<^sub>F\<^sub>M"
    using f4 by metis
  then show ?thesis
    by (metis ImpR_R)
qed
(*by (meson Bot_L DH_bdiam2_b DH_fdiam2_b D_IR1_b D_IR1_f E_L FS_bbox2 Fbox2_L Fdiam2_L IW_R Id_ag ImpR_R)*)

lemma c4_b: "\<turnstile>d ((a \<triangle>\<^sub>0 \<top>) \<rightarrow>\<^sub>F \<bottom>)\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M (a \<rhd>\<^sub>0 \<bottom>)\<^sub>S\<^sub>F\<^sub>M"
proof - 
  have "\<turnstile>d ((a \<triangle>\<^sub>0 \<top>) \<rightarrow>\<^sub>F \<bottom>)\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M (a)\<^sub>S\<^sub>F\<^sub>A \<rhd>\<^sub>0\<^sub>S (I\<^sub>S \<rightarrow>\<^sub>S (\<bottom>)\<^sub>S\<^sub>F\<^sub>M)"
    using Bot_L FS_fbox0 Fdiam0_R IW_R Id_fa ImpR_L Top_R by blast
  then show ?thesis
    using DH_bdiam0_b DH_bdiam0_f D_IL1_f D_IR1_b Fbox0_R I_1L_b by blast
qed

lemma c5_f: "\<turnstile>d (a \<triangle>\<^sub>0 \<bottom>)\<^sub>S\<^sub>F\<^sub>M  \<turnstile>\<^sub>F\<^sub>M (\<bottom>)\<^sub>S\<^sub>F\<^sub>M"
using Bot_L DH_fdiam0_b Fdiam0_L IW_R by blast

lemma c5_b: "\<turnstile>d (\<bottom>)\<^sub>S\<^sub>F\<^sub>M  \<turnstile>\<^sub>F\<^sub>M (a \<triangle>\<^sub>0 \<bottom>)\<^sub>S\<^sub>F\<^sub>M"
using [[simp_trace_new mode=full]] 
by (simp add: Bot_L IW_R)

lemma c6_f: "\<turnstile>d (a \<rhd>\<^sub>0 \<top>)\<^sub>S\<^sub>F\<^sub>M  \<turnstile>\<^sub>F\<^sub>M (\<top>)\<^sub>S\<^sub>F\<^sub>M"
using [[simp_trace_new mode=full]] 
by (simp add: IW_L Top_R)

lemma c6_b: "\<turnstile>d (\<top>)\<^sub>S\<^sub>F\<^sub>M  \<turnstile>\<^sub>F\<^sub>M (a \<rhd>\<^sub>0 \<top>)\<^sub>S\<^sub>F\<^sub>M"
using [[simp_trace_new mode=full]] 
by (simp add: DH_bdiam0_f Fbox0_R IW_L Top_R)

lemma c7_f: "\<turnstile>d (a \<rhd>\<^sub>0 (A \<and>\<^sub>F B))\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M ((a \<rhd>\<^sub>0 A) \<and>\<^sub>F (a \<rhd>\<^sub>0 B))\<^sub>S\<^sub>F\<^sub>M"
proof - 
  have f1:  "\<turnstile>d (a \<rhd>\<^sub>0 (A \<and>\<^sub>F B))\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M (a \<rhd>\<^sub>0 A)\<^sub>S\<^sub>F\<^sub>M"
    by (simp add: AderivesA And_L D_IR1_b Fbox0_L Fbox0_R Id_fa W_2L)
  have f2: "\<turnstile>d (a \<rhd>\<^sub>0 (A \<and>\<^sub>F B))\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M (a \<rhd>\<^sub>0 B)\<^sub>S\<^sub>F\<^sub>M"
    by (simp add: AderivesA And_L D_IL1_b Fbox0_L Fbox0_R Id_fa W_1L)
  show ?thesis
    using And_R C_L f1 f2 by blast
qed  

lemma c7_b: "\<turnstile>d ((a \<rhd>\<^sub>0 A) \<and>\<^sub>F (a \<rhd>\<^sub>0 B))\<^sub>S\<^sub>F\<^sub>M  \<turnstile>\<^sub>F\<^sub>M (a \<rhd>\<^sub>0 (A \<and>\<^sub>F B))\<^sub>S\<^sub>F\<^sub>M"
proof -
  have "\<turnstile>d (a)\<^sub>S\<^sub>F\<^sub>A \<triangleq>\<^sub>0\<^sub>S (a \<rhd>\<^sub>0 A)\<^sub>S\<^sub>F\<^sub>M  \<turnstile>\<^sub>F\<^sub>M (A)\<^sub>S\<^sub>F\<^sub>M"
    by (simp add: AderivesA DH_bdiam0_b Fbox0_L Id_fa)
  then show ?thesis
    by (simp add: AderivesA And_L And_R DH_bdiam0_b DH_bdiam0_f Fbox0_L Fbox0_R Id_fa Mon_bdiam0)
qed

lemma c8_f: "\<turnstile>d (a \<triangle>\<^sub>0 (A \<and>\<^sub>F B))\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M ((a \<triangle>\<^sub>0 A) \<and>\<^sub>F (a \<triangle>\<^sub>0 B))\<^sub>S\<^sub>F\<^sub>M"
by (metis And_L And_R C_L D_IL1_b D_IR1_b Fdiam0_L Fdiam0_R Id_fa W_1L W_2L AderivesA)

(*lemma c8_f_simple: "\<turnstile>d (a \<triangle>\<^sub>2 ((A)\<^sub>F \<and>\<^sub>F (B)\<^sub>F))\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M ((a \<triangle>\<^sub>2 (A)\<^sub>F) \<and>\<^sub>F (a \<triangle>\<^sub>2 (B)\<^sub>F) )\<^sub>S\<^sub>F\<^sub>M"
by (metis And_L And_R C_L D_IL1_b D_IR1_b Fdiam2_L Fdiam2_R Id_ag Id_fm W_1L W_2L)*)

lemma c8_b: "\<turnstile>d ((a \<triangle>\<^sub>0 A) \<and>\<^sub>F (a \<triangle>\<^sub>0 B))\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M (a \<triangle>\<^sub>0 (A \<and>\<^sub>F B))\<^sub>S\<^sub>F\<^sub>M"
proof -
  have "\<turnstile>d (a)\<^sub>S\<^sub>F\<^sub>A \<triangleq>\<^sub>0\<^sub>S (((a)\<^sub>S\<^sub>F\<^sub>A \<triangle>\<^sub>0\<^sub>S (A)\<^sub>S\<^sub>F\<^sub>M) ;\<^sub>S ((a)\<^sub>S\<^sub>F\<^sub>A \<triangle>\<^sub>0\<^sub>S (B)\<^sub>S\<^sub>F\<^sub>M)) \<turnstile>\<^sub>F\<^sub>M (A \<and>\<^sub>F B)\<^sub>S\<^sub>F\<^sub>M"
    by (simp add: AderivesA And_R Balance Conj_fdiam0 DH_bdiam0_b)
  then show ?thesis
    by (simp add: And_L Conj_bdiam0 Conj_fdiam0 D_IL1_b D_IL1_f E_L Fdiam0_L Fdiam0_R Id_fa)
qed

lemma c9_f: "\<turnstile>d (a \<triangle>\<^sub>0 (A \<or>\<^sub>F B))\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M ((a \<triangle>\<^sub>0 A) \<or>\<^sub>F (a \<triangle>\<^sub>0 B))\<^sub>S\<^sub>F\<^sub>M"
proof -
  have "\<turnstile>d (A)\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M (a)\<^sub>S\<^sub>F\<^sub>A \<unrhd>\<^sub>0\<^sub>S (a \<triangle>\<^sub>0 A)\<^sub>S\<^sub>F\<^sub>M"
    by (simp add: AderivesA DH_fdiam0_f Fdiam0_R Id_fa)
  then show ?thesis
    by (simp add: AderivesA DH_fdiam0_b DH_fdiam0_f Fdiam0_L Fdiam0_R Id_fa Mon_bbox0 Or_L Or_R)
qed

lemma c9_b: "\<turnstile>d ((a \<triangle>\<^sub>0 A) \<or>\<^sub>F (a \<triangle>\<^sub>0 B))\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M (a \<triangle>\<^sub>0 (A \<or>\<^sub>F B))\<^sub>S\<^sub>F\<^sub>M"
proof -
  have f1: "\<turnstile>d (a \<triangle>\<^sub>0 A)\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M (a \<triangle>\<^sub>0 (A \<or>\<^sub>F B))\<^sub>S\<^sub>F\<^sub>M "
    by (simp add: AderivesA D_IR2_b Fdiam0_L Fdiam0_R Id_fa Or_R W_2R)
  have f2: "\<turnstile>d (a \<triangle>\<^sub>0 B)\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M (a \<triangle>\<^sub>0 (A \<or>\<^sub>F B))\<^sub>S\<^sub>F\<^sub>M "
    by (simp add: AderivesA D_IL2_b Fdiam0_L Fdiam0_R Id_fa Or_R W_1R)
  show ?thesis
    using C_R Or_L f1 f2 by blast
qed
  
lemma c10_f: "\<turnstile>d (a \<rhd>\<^sub>0 (A \<or>\<^sub>F B))\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M (a \<triangle>\<^sub>0 \<top>)\<^sub>S\<^sub>F\<^sub>M \<rightarrow>\<^sub>S ((a \<triangle>\<^sub>0 A) \<or>\<^sub>F (a \<triangle>\<^sub>0 B))\<^sub>S\<^sub>F\<^sub>M"
sledgehammer
proof - 
  have "\<turnstile>d (a)\<^sub>S\<^sub>F\<^sub>A \<triangle>\<^sub>0\<^sub>S (A \<or>\<^sub>F B)\<^sub>S\<^sub>F\<^sub>M  \<turnstile>\<^sub>F\<^sub>M ((a \<triangle>\<^sub>0 A) \<or>\<^sub>F (a \<triangle>\<^sub>0 B))\<^sub>S\<^sub>F\<^sub>M "
    by (simp add: AderivesA DH_fdiam0_b DH_fdiam0_f Fdiam0_R Id_fa Mon_bbox0 Or_L Or_R)
  then show ?thesis
    by (simp add: DH_bdiam0_b DH_fdiam0_b DH_fdiam0_f D_IR1_b D_IR1_f E_L FS_bbox0 Fbox0_L Fdiam0_L W_2L derivable.intros(3))
qed

lemma c10_b: "\<turnstile>d (a \<triangle>\<^sub>0 \<top>)\<^sub>S\<^sub>F\<^sub>M \<rightarrow>\<^sub>S ((a \<triangle>\<^sub>0 A) \<or>\<^sub>F (a \<triangle>\<^sub>0 B))\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M (a \<rhd>\<^sub>0 (A \<or>\<^sub>F B))\<^sub>S\<^sub>F\<^sub>M"
by (meson DH_bdiam0_f DH_fdiam0_f FS_bdiam0 Fbox0_R Fdiam0_R IW_L Id_fa Top_R W_2R)

lemma c11_f: "\<turnstile>d (a \<triangle>\<^sub>0 (A \<rightarrow>\<^sub>F B))\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M ((a \<triangle>\<^sub>0 \<top>) \<and>\<^sub>F ((a \<triangle>\<^sub>0 A)  \<rightarrow>\<^sub>F (a \<triangle>\<^sub>0 B)))\<^sub>S\<^sub>F\<^sub>M"
proof - 
  have "\<turnstile>d (a)\<^sub>S\<^sub>F\<^sub>A \<triangle>\<^sub>0\<^sub>S (A \<rightarrow>\<^sub>F B)\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M (((a \<triangle>\<^sub>0 A)  \<rightarrow>\<^sub>F (a \<triangle>\<^sub>0 B)))\<^sub>S\<^sub>F\<^sub>M"
    by (simp add: AderivesA Balance Conj_fdiam0 DH_bdiam0_b D_IR1_b D_IR1_f Fdiam0_L Fdiam0_R Id_fa ImpR_L ImpR_R)
  then show ?thesis
    by (meson And_R C_L Fdiam0_L Fdiam0_R IW_L Id_fa Top_R)
qed

lemma c11_b: "\<turnstile>d ((a \<triangle>\<^sub>0 \<top>) \<and>\<^sub>F ((a \<triangle>\<^sub>0 A) \<rightarrow>\<^sub>F (a \<triangle>\<^sub>0 B)))\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M (a \<triangle>\<^sub>0 (A \<rightarrow>\<^sub>F B))\<^sub>S\<^sub>F\<^sub>M"
proof - 
  have "\<turnstile>d (a)\<^sub>S\<^sub>F\<^sub>A \<triangle>\<^sub>0\<^sub>S ((a)\<^sub>S\<^sub>F\<^sub>A \<triangleq>\<^sub>0\<^sub>S ((a \<triangle>\<^sub>0 A) \<rightarrow>\<^sub>F (a \<triangle>\<^sub>0 B))\<^sub>S\<^sub>F\<^sub>M) \<turnstile>\<^sub>F\<^sub>M (a \<triangle>\<^sub>0 (A \<rightarrow>\<^sub>F B))\<^sub>S\<^sub>F\<^sub>M"
    by (simp add: AderivesA Balance DH_bdiam0_b FS_fbox0 Fdiam0_L Fdiam0_R Id_fa ImpR_L ImpR_R)
  then show ?thesis
    by (simp add: And_L DH_fdiam0_b DH_fdiam0_f D_IR1_b E_L FS_bbox0 Fdiam0_L W_2L)
qed

lemma c12_f: "\<turnstile>d (a \<rhd>\<^sub>0 (A \<rightarrow>\<^sub>F B))\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M ((a \<triangle>\<^sub>0 A) \<rightarrow>\<^sub>F (a \<triangle>\<^sub>0 B))\<^sub>S\<^sub>F\<^sub>M"
proof -
  have "\<turnstile>d (a)\<^sub>S\<^sub>F\<^sub>A \<triangleq>\<^sub>0\<^sub>S (a \<rhd>\<^sub>0 (A \<rightarrow>\<^sub>F B))\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M (a)\<^sub>S\<^sub>F\<^sub>A \<unrhd>\<^sub>0\<^sub>S (((a)\<^sub>S\<^sub>F\<^sub>A \<triangle>\<^sub>0\<^sub>S (A)\<^sub>S\<^sub>F\<^sub>M) \<rightarrow>\<^sub>S (a \<triangle>\<^sub>0 B)\<^sub>S\<^sub>F\<^sub>M)"
    by (simp add: AderivesA Balance DH_bdiam0_b DH_fdiam0_f FS_bbox0 Fbox0_L Fdiam0_R Id_fa ImpR_L)
  then show ?thesis
    by (simp add: Conj_fdiam0 DH_fdiam0_b D_IR1_b D_IR1_f E_L Fdiam0_L ImpR_R Mon_fdiam0)
qed

lemma c12_b: "\<turnstile>d ((a \<triangle>\<^sub>0 A) \<rightarrow>\<^sub>F (a \<triangle>\<^sub>0 B))\<^sub>S\<^sub>F\<^sub>M  \<turnstile>\<^sub>F\<^sub>M (a \<rhd>\<^sub>0 (A \<rightarrow>\<^sub>F B))\<^sub>S\<^sub>F\<^sub>M"
by (simp add: AderivesA Balance DH_bdiam0_b DH_bdiam0_f FS_fbox0 Fbox0_R Fdiam0_L Fdiam0_R Id_fa ImpR_L ImpR_R)

lemma c13: "\<turnstile>d ((a \<triangle>\<^sub>0 \<top>) \<and>\<^sub>F (ag \<triangle>\<^sub>2 ((ag \<triangleq>\<^sub>3 a) \<triangle>\<^sub>1 A)))\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M (a \<triangle>\<^sub>0 (ag \<triangle>\<^sub>2 A))\<^sub>S\<^sub>F\<^sub>M "
proof - 
  have "\<turnstile>d ((ag \<triangleq>\<^sub>3 a) \<triangle>\<^sub>1 A)\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M (ag)\<^sub>S\<^sub>A\<^sub>G \<unrhd>\<^sub>2\<^sub>S (((a)\<^sub>S\<^sub>F\<^sub>A \<triangle>\<^sub>0\<^sub>S I\<^sub>S) \<rightarrow>\<^sub>S (a \<triangle>\<^sub>0 (ag \<triangle>\<^sub>2 A))\<^sub>S\<^sub>F\<^sub>M)"
sledgehammer[timeout=600]
  then show ?thesis
qed

lemma c14: "\<turnstile>d (a \<rhd>\<^sub>0 (ag \<rhd>\<^sub>2 A))\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M ((a \<triangle>\<^sub>0 \<top>) \<rightarrow>\<^sub>F (ag \<rhd>\<^sub>2 ((ag \<triangleq>\<^sub>3  a) \<rhd>\<^sub>1 A )))\<^sub>S\<^sub>F\<^sub>M"
sledgehammer[timeout=600]
sorry

lemma c15: "\<turnstile>d (a \<triangle>\<^sub>0 (ag \<rhd>\<^sub>2 A))\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M ((a \<triangle>\<^sub>0 \<top>) \<and>\<^sub>F (ag \<rhd>\<^sub>2 ((ag \<triangleq>\<^sub>3 a) \<rhd>\<^sub>1 A )))\<^sub>S\<^sub>F\<^sub>M"
sorry

lemma c16: "\<turnstile>d ((a \<triangle>\<^sub>0 \<top>) \<and>\<^sub>F (ag \<rhd>\<^sub>2 ((ag \<triangleq>\<^sub>3 a) \<rhd>\<^sub>1 A)))\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M (a \<triangle>\<^sub>0 (ag \<rhd>\<^sub>2 A))\<^sub>S\<^sub>F\<^sub>M"
sorry