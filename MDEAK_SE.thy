theory MDEAK_SE
imports Main MDEAK_Core_SE
begin

fun is_act_mod_left :: "Formula_S \<Rightarrow> Atprop option" where
"is_act_mod_left (Formula_Atomic_S (Formula_Atprop p)) = Some p"|
"is_act_mod_left (Formula_Fdiam0_S _ s) = is_act_mod_left s"|
"is_act_mod_left (Formula_Bdiam0_S _ s) = is_act_mod_left s"|
"is_act_mod_left _ = None"

fun is_act_mod_right :: "Formula_S \<Rightarrow> Atprop option" where
"is_act_mod_right (Formula_Atomic_S (Formula_Atprop p)) = Some p"|
"is_act_mod_right (Formula_Fbox0_S _ s) = is_act_mod_right s"|
"is_act_mod_right (Formula_Bbox0_S _ s) = is_act_mod_right s"|
"is_act_mod_right _ = None"

fun atom :: "Sequent \<Rightarrow> bool" where
"atom (l \<turnstile>\<^sub>F\<^sub>M r) = 
 ( (is_act_mod_left l) \<noteq> None \<and>
 (is_act_mod_right r) \<noteq> None \<and> 
 (is_act_mod_left l) = (is_act_mod_right r) )"|
"atom (l \<turnstile>\<^sub>F\<^sub>A r) = False"|
"atom (l \<turnstile>\<^sub>A\<^sub>G r) = False"|
"atom (l \<turnstile>\<^sub>A\<^sub>C r) = False"

inductive derivable :: "Sequent \<Rightarrow> bool" ("\<turnstile>d _" [210] 200) where
(* Structural Rules *)
Id_fm:        "\<turnstile>d (p\<^sub>F)\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M (p\<^sub>F)\<^sub>S\<^sub>F\<^sub>M"|
Id_ag:        "\<turnstile>d a\<^sub>S\<^sub>A\<^sub>G \<turnstile>\<^sub>A\<^sub>G a\<^sub>S\<^sub>A\<^sub>G"|
Id_ac:        "\<turnstile>d a\<^sub>S\<^sub>A\<^sub>C \<turnstile>\<^sub>A\<^sub>C a\<^sub>S\<^sub>A\<^sub>C"|
Cut_fm:       "(Formula f) \<Longrightarrow> \<turnstile>d X \<turnstile>\<^sub>F\<^sub>M f \<^sub>S\<^sub>F\<^sub>M \<Longrightarrow> \<turnstile>d f \<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M Y \<Longrightarrow> \<turnstile>d X \<turnstile>\<^sub>F\<^sub>M Y"|
Cut_ag:       "(Agent a) \<Longrightarrow> \<turnstile>d x \<turnstile>\<^sub>A\<^sub>G a \<^sub>S\<^sub>A\<^sub>G \<Longrightarrow> \<turnstile>d a \<^sub>S\<^sub>A\<^sub>G \<turnstile>\<^sub>A\<^sub>G y \<Longrightarrow> \<turnstile>d x \<turnstile>\<^sub>A\<^sub>G y"|
Cut_ac:       "(Action a) \<Longrightarrow> \<turnstile>d x \<turnstile>\<^sub>A\<^sub>C a \<^sub>S\<^sub>A\<^sub>C \<Longrightarrow> \<turnstile>d a \<^sub>S\<^sub>A\<^sub>C \<turnstile>\<^sub>A\<^sub>C y \<Longrightarrow> \<turnstile>d x \<turnstile>\<^sub>A\<^sub>C y"|
Cut_fa:       "(Funaction a) \<Longrightarrow> \<turnstile>d x \<turnstile>\<^sub>F\<^sub>A a \<^sub>S\<^sub>F\<^sub>A \<Longrightarrow> \<turnstile>d a \<^sub>S\<^sub>F\<^sub>A \<turnstile>\<^sub>F\<^sub>A y \<Longrightarrow> \<turnstile>d x \<turnstile>\<^sub>F\<^sub>A y"|
I_1L_f:       "\<turnstile>d X \<turnstile>\<^sub>F\<^sub>M Y \<Longrightarrow> \<turnstile>d I\<^sub>S \<turnstile>\<^sub>F\<^sub>M (Y \<leftarrow>\<^sub>S X)"|
I_1L_b:       "\<turnstile>d I\<^sub>S \<turnstile>\<^sub>F\<^sub>M (Y \<leftarrow>\<^sub>S X) \<Longrightarrow> \<turnstile>d X \<turnstile>\<^sub>F\<^sub>M Y"|
I_1R_f:       "\<turnstile>d X \<turnstile>\<^sub>F\<^sub>M Y \<Longrightarrow> \<turnstile>d (X \<leftarrow>\<^sub>S Y) \<turnstile>\<^sub>F\<^sub>M I\<^sub>S"|
I_1R_b:       "\<turnstile>d (X \<leftarrow>\<^sub>S Y) \<turnstile>\<^sub>F\<^sub>M I\<^sub>S \<Longrightarrow> \<turnstile>d X \<turnstile>\<^sub>F\<^sub>M Y"|
I_2L_f:       "\<turnstile>d X \<turnstile>\<^sub>F\<^sub>M Y \<Longrightarrow> \<turnstile>d I\<^sub>S \<turnstile>\<^sub>F\<^sub>M (X \<rightarrow>\<^sub>S Y)"|
I_2L_b:       "\<turnstile>d I\<^sub>S \<turnstile>\<^sub>F\<^sub>M (X \<rightarrow>\<^sub>S Y) \<Longrightarrow> \<turnstile>d X \<turnstile>\<^sub>F\<^sub>M Y"|
I_2R_f:       "\<turnstile>d X \<turnstile>\<^sub>F\<^sub>M Y \<Longrightarrow> \<turnstile>d (Y \<rightarrow>\<^sub>S X) \<turnstile>\<^sub>F\<^sub>M I\<^sub>S"|
I_2R_b:       "\<turnstile>d (Y \<rightarrow>\<^sub>S X) \<turnstile>\<^sub>F\<^sub>M I\<^sub>S \<Longrightarrow> \<turnstile>d X \<turnstile>\<^sub>F\<^sub>M Y"|
IW_L:         "\<turnstile>d I\<^sub>S \<turnstile>\<^sub>F\<^sub>M X \<Longrightarrow> \<turnstile>d Y \<turnstile>\<^sub>F\<^sub>M X"|
IW_R:         "\<turnstile>d X \<turnstile>\<^sub>F\<^sub>M I\<^sub>S \<Longrightarrow> \<turnstile>d X \<turnstile>\<^sub>F\<^sub>M Y"|
W_1L:         "\<turnstile>d X \<turnstile>\<^sub>F\<^sub>M Z \<Longrightarrow> \<turnstile>d Y \<turnstile>\<^sub>F\<^sub>M (Z \<leftarrow>\<^sub>S X)"|
W_1R:         "\<turnstile>d X \<turnstile>\<^sub>F\<^sub>M Z \<Longrightarrow> \<turnstile>d (X \<leftarrow>\<^sub>S Z) \<turnstile>\<^sub>F\<^sub>M Y"|
W_2L:         "\<turnstile>d X \<turnstile>\<^sub>F\<^sub>M Z \<Longrightarrow> \<turnstile>d Y \<turnstile>\<^sub>F\<^sub>M (X \<rightarrow>\<^sub>S Z)"|
W_2R:         "\<turnstile>d X \<turnstile>\<^sub>F\<^sub>M Z \<Longrightarrow> \<turnstile>d (Z \<rightarrow>\<^sub>S X) \<turnstile>\<^sub>F\<^sub>M Y"|
C_L:          "\<turnstile>d (X ;\<^sub>S X) \<turnstile>\<^sub>F\<^sub>M Y \<Longrightarrow> \<turnstile>d X \<turnstile>\<^sub>F\<^sub>M Y"|
C_R:          "\<turnstile>d Y \<turnstile>\<^sub>F\<^sub>M (X ;\<^sub>S X) \<Longrightarrow> \<turnstile>d Y \<turnstile>\<^sub>F\<^sub>M X"|
E_L:          "\<turnstile>d (Y ;\<^sub>S X) \<turnstile>\<^sub>F\<^sub>M Z \<Longrightarrow> \<turnstile>d (X ;\<^sub>S Y) \<turnstile>\<^sub>F\<^sub>M Z"|
E_R:          "\<turnstile>d Z \<turnstile>\<^sub>F\<^sub>M (X ;\<^sub>S Y) \<Longrightarrow> \<turnstile>d Z  \<turnstile>\<^sub>F\<^sub>M (Y ;\<^sub>S X)"|
A_L:          "\<turnstile>d (X ;\<^sub>S (Y ;\<^sub>S Z)) \<turnstile>\<^sub>F\<^sub>M W \<Longrightarrow> \<turnstile>d ((X ;\<^sub>S Y) ;\<^sub>S Z) \<turnstile>\<^sub>F\<^sub>M W"| 
A_R:          "\<turnstile>d W  \<turnstile>\<^sub>F\<^sub>M ((Z ;\<^sub>S Y) ;\<^sub>S X) \<Longrightarrow> \<turnstile>d W  \<turnstile>\<^sub>F\<^sub>M (Z ;\<^sub>S (Y ;\<^sub>S X))"|
(* Display Postulates *)
D_IL1_f:      "\<turnstile>d (X ;\<^sub>S Y) \<turnstile>\<^sub>F\<^sub>M Z \<Longrightarrow> \<turnstile>d  X \<turnstile>\<^sub>F\<^sub>M Z \<leftarrow>\<^sub>S Y"|
D_IL1_b:      "\<turnstile>d  X \<turnstile>\<^sub>F\<^sub>M Z \<leftarrow>\<^sub>S Y \<Longrightarrow> \<turnstile>d (X ;\<^sub>S Y) \<turnstile>\<^sub>F\<^sub>M Z"|
D_IL2_f:      "\<turnstile>d Z \<turnstile>\<^sub>F\<^sub>M (X ;\<^sub>S Y) \<Longrightarrow> \<turnstile>d  Z \<leftarrow>\<^sub>S Y  \<turnstile>\<^sub>F\<^sub>M X"|
D_IL2_b:      "\<turnstile>d  Z \<leftarrow>\<^sub>S Y  \<turnstile>\<^sub>F\<^sub>M X \<Longrightarrow> \<turnstile>d Z \<turnstile>\<^sub>F\<^sub>M (X ;\<^sub>S Y)"|
D_IR1_f:      "\<turnstile>d (X ;\<^sub>S Y) \<turnstile>\<^sub>F\<^sub>M Z \<Longrightarrow> \<turnstile>d  Y \<turnstile>\<^sub>F\<^sub>M X \<rightarrow>\<^sub>S Z"|
D_IR1_b:      "\<turnstile>d  Y \<turnstile>\<^sub>F\<^sub>M X \<rightarrow>\<^sub>S Z \<Longrightarrow> \<turnstile>d (X ;\<^sub>S Y) \<turnstile>\<^sub>F\<^sub>M Z"|
D_IR2_f:      "\<turnstile>d Z \<turnstile>\<^sub>F\<^sub>M (X ;\<^sub>S Y) \<Longrightarrow> \<turnstile>d  X \<rightarrow>\<^sub>S Z \<turnstile>\<^sub>F\<^sub>M Y"|
D_IR2_b:      "\<turnstile>d  X \<rightarrow>\<^sub>S Z \<turnstile>\<^sub>F\<^sub>M Y \<Longrightarrow> \<turnstile>d Z \<turnstile>\<^sub>F\<^sub>M (X ;\<^sub>S Y)"|
(* Grishin Rules *)
Gr_L_f:       "\<turnstile>d X \<rightarrow>\<^sub>S (Y ;\<^sub>S Z) \<turnstile>\<^sub>F\<^sub>M W \<Longrightarrow> \<turnstile>d (X \<rightarrow>\<^sub>S Y) ;\<^sub>S Z \<turnstile>\<^sub>F\<^sub>M W"|
Gr_L_b:       "\<turnstile>d (X \<rightarrow>\<^sub>S Y) ;\<^sub>S Z \<turnstile>\<^sub>F\<^sub>M W \<Longrightarrow> \<turnstile>d X \<rightarrow>\<^sub>S (Y ;\<^sub>S Z) \<turnstile>\<^sub>F\<^sub>M W"|
Gr_R_f:       "\<turnstile>d W  \<turnstile>\<^sub>F\<^sub>M X \<rightarrow>\<^sub>S (Y ;\<^sub>S Z) \<Longrightarrow> \<turnstile>d W \<turnstile>\<^sub>F\<^sub>M (X \<rightarrow>\<^sub>S Y) ;\<^sub>S Z"|
Gr_R_b:       "\<turnstile>d W \<turnstile>\<^sub>F\<^sub>M (X \<rightarrow>\<^sub>S Y) ;\<^sub>S Z \<Longrightarrow> \<turnstile>d W  \<turnstile>\<^sub>F\<^sub>M X \<rightarrow>\<^sub>S (Y ;\<^sub>S Z)"|
(* Operational Rules *)
Bot_L:        "\<turnstile>d \<bottom>\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M I\<^sub>S"|
Bot_R:        "\<turnstile>d X \<turnstile>\<^sub>F\<^sub>M I\<^sub>S \<Longrightarrow> \<turnstile>d X \<turnstile>\<^sub>F\<^sub>M \<bottom>\<^sub>S\<^sub>F\<^sub>M"|
Top_L:        "\<turnstile>d I\<^sub>S \<turnstile>\<^sub>F\<^sub>M X \<Longrightarrow> \<turnstile>d \<top>\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M X"|
Top_R:        "\<turnstile>d I\<^sub>S  \<turnstile>\<^sub>F\<^sub>M \<top> \<^sub>S\<^sub>F\<^sub>M"|
And_L:        "\<turnstile>d (A\<^sub>S\<^sub>F\<^sub>M) ;\<^sub>S (B\<^sub>S\<^sub>F\<^sub>M) \<turnstile>\<^sub>F\<^sub>M Z \<Longrightarrow> \<turnstile>d (A\<and>\<^sub>FB)\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M Z"|
And_R:        "\<turnstile>d X \<turnstile>\<^sub>F\<^sub>M (A\<^sub>S\<^sub>F\<^sub>M) \<Longrightarrow> \<turnstile>d Y \<turnstile>\<^sub>F\<^sub>M (B\<^sub>S\<^sub>F\<^sub>M) \<Longrightarrow> \<turnstile>d X ;\<^sub>S Y \<turnstile>\<^sub>F\<^sub>M (A\<and>\<^sub>FB)\<^sub>S\<^sub>F\<^sub>M"|
Or_L:         "\<turnstile>d A\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M X \<Longrightarrow> \<turnstile>d B\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M Y \<Longrightarrow> \<turnstile>d (A\<or>\<^sub>FB)\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M X ;\<^sub>S Y"|
Or_R:         "\<turnstile>d Z \<turnstile>\<^sub>F\<^sub>M A\<^sub>S\<^sub>F\<^sub>M ;\<^sub>S B\<^sub>S\<^sub>F\<^sub>M \<Longrightarrow> \<turnstile>d Z \<turnstile>\<^sub>F\<^sub>M (A\<or>\<^sub>FB)\<^sub>S\<^sub>F\<^sub>M"|
ImpL_L:       "\<turnstile>d B\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M Y \<Longrightarrow> \<turnstile>d X \<turnstile>\<^sub>F\<^sub>M A\<^sub>S\<^sub>F\<^sub>M \<Longrightarrow> \<turnstile>d (B \<leftarrow>\<^sub>F A)\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M Y \<leftarrow>\<^sub>S X"|
ImpL_R:       "\<turnstile>d Z \<turnstile>\<^sub>F\<^sub>M B\<^sub>S\<^sub>F\<^sub>M \<leftarrow>\<^sub>S A\<^sub>S\<^sub>F\<^sub>M \<Longrightarrow> \<turnstile>d Z \<turnstile>\<^sub>F\<^sub>M (B \<leftarrow>\<^sub>F A)\<^sub>S\<^sub>F\<^sub>M"|
DimpL_L:      "\<turnstile>d B\<^sub>S\<^sub>F\<^sub>M \<leftarrow>\<^sub>S A\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M Z \<Longrightarrow> \<turnstile>d (B-<A)\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M Z"|
DimpL_R:      "\<turnstile>d Y \<turnstile>\<^sub>F\<^sub>M B\<^sub>S\<^sub>F\<^sub>M \<Longrightarrow> \<turnstile>d A\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M X \<Longrightarrow> \<turnstile>d Y \<leftarrow>\<^sub>S X \<turnstile>\<^sub>F\<^sub>M (B-<A)\<^sub>S\<^sub>F\<^sub>M"|
ImpR_L:       "\<turnstile>d X \<turnstile>\<^sub>F\<^sub>M A\<^sub>S\<^sub>F\<^sub>M \<Longrightarrow> \<turnstile>d B\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M Y \<Longrightarrow> \<turnstile>d (A \<rightarrow>\<^sub>F B)\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M X \<rightarrow>\<^sub>S Y"|
ImpR_R:       "\<turnstile>d Z \<turnstile>\<^sub>F\<^sub>M A\<^sub>S\<^sub>F\<^sub>M \<rightarrow>\<^sub>S B\<^sub>S\<^sub>F\<^sub>M \<Longrightarrow> \<turnstile>d Z \<turnstile>\<^sub>F\<^sub>M (A \<rightarrow>\<^sub>F B)\<^sub>S\<^sub>F\<^sub>M"|
DimpR_L:      "\<turnstile>d A\<^sub>S\<^sub>F\<^sub>M \<rightarrow>\<^sub>S B\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M Z \<Longrightarrow> \<turnstile>d (A >- B)\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M Z"|
DimpR_R:      "\<turnstile>d A\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M X \<Longrightarrow> \<turnstile>d Y \<turnstile>\<^sub>F\<^sub>M B\<^sub>S\<^sub>F\<^sub>M \<Longrightarrow> \<turnstile>d X \<rightarrow>\<^sub>S Y \<turnstile>\<^sub>F\<^sub>M (A >- B)\<^sub>S\<^sub>F\<^sub>M"|
(* Heterogeneous Operational Rules *)
Fdiam0_L:     "\<turnstile>d a\<^sub>S\<^sub>F\<^sub>A \<triangle>\<^sub>0\<^sub>S B\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M Z \<Longrightarrow> \<turnstile>d (a \<triangle>\<^sub>0 B)\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M Z"|
Fdiam0_R:     "\<turnstile>d x \<turnstile>\<^sub>F\<^sub>A a\<^sub>S\<^sub>F\<^sub>A \<Longrightarrow> \<turnstile>d Y \<turnstile>\<^sub>F\<^sub>M B\<^sub>S\<^sub>F\<^sub>M \<Longrightarrow> \<turnstile>d x \<triangle>\<^sub>0\<^sub>S Y \<turnstile>\<^sub>F\<^sub>M (a \<triangle>\<^sub>0 B)\<^sub>S\<^sub>F\<^sub>M"|
Bdiam0_L:     "\<turnstile>d a\<^sub>S\<^sub>F\<^sub>A \<triangleq>\<^sub>0\<^sub>S B\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M Z \<Longrightarrow> \<turnstile>d (a \<triangleq>\<^sub>0 B)\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M Z"|
Bdiam0_R:     "\<turnstile>d x \<turnstile>\<^sub>F\<^sub>A a\<^sub>S\<^sub>F\<^sub>A \<Longrightarrow> \<turnstile>d Y \<turnstile>\<^sub>F\<^sub>M B\<^sub>S\<^sub>F\<^sub>M \<Longrightarrow> \<turnstile>d x \<triangleq>\<^sub>0\<^sub>S Y \<turnstile>\<^sub>F\<^sub>M (a \<triangleq>\<^sub>0 B)\<^sub>S\<^sub>F\<^sub>M"|
Fdiam1_L:     "\<turnstile>d a\<^sub>S\<^sub>A\<^sub>C \<triangle>\<^sub>1\<^sub>S B\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M Z \<Longrightarrow> \<turnstile>d (a \<triangle>\<^sub>1 B)\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M Z"|
Fdiam1_R:     "\<turnstile>d x \<turnstile>\<^sub>A\<^sub>C a\<^sub>S\<^sub>A\<^sub>C \<Longrightarrow> \<turnstile>d Y \<turnstile>\<^sub>F\<^sub>M B\<^sub>S\<^sub>F\<^sub>M \<Longrightarrow> \<turnstile>d x \<triangle>\<^sub>1\<^sub>S Y \<turnstile>\<^sub>F\<^sub>M (a \<triangle>\<^sub>1 B)\<^sub>S\<^sub>F\<^sub>M"|
Bdiam1_L:     "\<turnstile>d a\<^sub>S\<^sub>A\<^sub>C \<triangleq>\<^sub>1\<^sub>S B\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M Z \<Longrightarrow> \<turnstile>d (a \<triangleq>\<^sub>1 B)\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M Z"|
Bdiam1_R:     "\<turnstile>d x \<turnstile>\<^sub>A\<^sub>C a\<^sub>S\<^sub>A\<^sub>C \<Longrightarrow> \<turnstile>d Y \<turnstile>\<^sub>F\<^sub>M B\<^sub>S\<^sub>F\<^sub>M \<Longrightarrow> \<turnstile>d x \<triangleq>\<^sub>1\<^sub>S Y \<turnstile>\<^sub>F\<^sub>M (a \<triangleq>\<^sub>1 B)\<^sub>S\<^sub>F\<^sub>M"|
Fdiam2_L:     "\<turnstile>d a\<^sub>S\<^sub>A\<^sub>G \<triangle>\<^sub>2\<^sub>S B\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M Z \<Longrightarrow> \<turnstile>d (a \<triangle>\<^sub>2 B)\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M Z"|
Fdiam2_R:     "\<turnstile>d x \<turnstile>\<^sub>A\<^sub>G a\<^sub>S\<^sub>A\<^sub>G \<Longrightarrow> \<turnstile>d Y \<turnstile>\<^sub>F\<^sub>M B\<^sub>S\<^sub>F\<^sub>M \<Longrightarrow> \<turnstile>d x \<triangle>\<^sub>2\<^sub>S Y \<turnstile>\<^sub>F\<^sub>M (a \<triangle>\<^sub>2 B)\<^sub>S\<^sub>F\<^sub>M"|
Bdiam2_L:     "\<turnstile>d a\<^sub>S\<^sub>A\<^sub>G \<triangleq>\<^sub>2\<^sub>S B\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M Z \<Longrightarrow> \<turnstile>d (a \<triangleq>\<^sub>2 B)\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M Z"|
Bdiam2_R:     "\<turnstile>d x \<turnstile>\<^sub>A\<^sub>G a\<^sub>S\<^sub>A\<^sub>G \<Longrightarrow> \<turnstile>d Y \<turnstile>\<^sub>F\<^sub>M B\<^sub>S\<^sub>F\<^sub>M \<Longrightarrow> \<turnstile>d x \<triangleq>\<^sub>2\<^sub>S Y \<turnstile>\<^sub>F\<^sub>M (a \<triangleq>\<^sub>2 B)\<^sub>S\<^sub>F\<^sub>M"|
Fdiam3_L:     "\<turnstile>d a\<^sub>S\<^sub>A\<^sub>G \<triangle>\<^sub>3\<^sub>S b\<^sub>S\<^sub>F\<^sub>A \<turnstile>\<^sub>A\<^sub>C z \<Longrightarrow> \<turnstile>d (a \<triangle>\<^sub>3 b)\<^sub>S\<^sub>A\<^sub>C \<turnstile>\<^sub>A\<^sub>C z"|
Fdiam3_R:     "\<turnstile>d x \<turnstile>\<^sub>A\<^sub>G a\<^sub>S\<^sub>A\<^sub>G \<Longrightarrow> \<turnstile>d y \<turnstile>\<^sub>F\<^sub>A b\<^sub>S\<^sub>F\<^sub>A \<Longrightarrow> \<turnstile>d x \<triangle>\<^sub>3\<^sub>S y \<turnstile>\<^sub>A\<^sub>C (a \<triangle>\<^sub>3 B)\<^sub>S\<^sub>A\<^sub>C"|
Bdiam3_L:     "\<turnstile>d a\<^sub>S\<^sub>A\<^sub>G \<triangleq>\<^sub>3\<^sub>S b\<^sub>S\<^sub>F\<^sub>A \<turnstile>\<^sub>A\<^sub>C z \<Longrightarrow> \<turnstile>d (a \<triangleq>\<^sub>3 b)\<^sub>S\<^sub>A\<^sub>C \<turnstile>\<^sub>A\<^sub>C z"|
Bdiam3_R:     "\<turnstile>d x \<turnstile>\<^sub>A\<^sub>G a\<^sub>S\<^sub>A\<^sub>G \<Longrightarrow> \<turnstile>d y \<turnstile>\<^sub>F\<^sub>A b\<^sub>S\<^sub>F\<^sub>A \<Longrightarrow> \<turnstile>d x \<triangleq>\<^sub>3\<^sub>S y \<turnstile>\<^sub>A\<^sub>C (a \<triangleq>\<^sub>3 B)\<^sub>S\<^sub>A\<^sub>C"|
Fbox0_L:      "\<turnstile>d x \<turnstile>\<^sub>F\<^sub>A a\<^sub>S\<^sub>F\<^sub>A \<Longrightarrow> \<turnstile>d B\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M Y \<Longrightarrow> \<turnstile>d (a \<rhd>\<^sub>0 B)\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M x \<rhd>\<^sub>0\<^sub>S Y"|
Fbox0_R:      "\<turnstile>d Z \<turnstile>\<^sub>F\<^sub>M a\<^sub>S\<^sub>F\<^sub>A \<rhd>\<^sub>0\<^sub>S B\<^sub>S\<^sub>F\<^sub>M \<Longrightarrow> \<turnstile>d Z \<turnstile>\<^sub>F\<^sub>M (a \<rhd>\<^sub>0 B)\<^sub>S\<^sub>F\<^sub>M"|
Bbox0_L:      "\<turnstile>d x \<turnstile>\<^sub>F\<^sub>A a\<^sub>S\<^sub>F\<^sub>A \<Longrightarrow> \<turnstile>d B\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M Y \<Longrightarrow> \<turnstile>d (a \<unrhd>\<^sub>0 B)\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M x \<unrhd>\<^sub>0\<^sub>S Y"|
Bbox0_R:      "\<turnstile>d Z \<turnstile>\<^sub>F\<^sub>M a\<^sub>S\<^sub>F\<^sub>A \<unrhd>\<^sub>0\<^sub>S B\<^sub>S\<^sub>F\<^sub>M \<Longrightarrow> \<turnstile>d Z \<turnstile>\<^sub>F\<^sub>M (a \<unrhd>\<^sub>0 B)\<^sub>S\<^sub>F\<^sub>M"|
Fbox1_L:      "\<turnstile>d x \<turnstile>\<^sub>A\<^sub>C a\<^sub>S\<^sub>A\<^sub>C \<Longrightarrow> \<turnstile>d B\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M Y \<Longrightarrow> \<turnstile>d (a \<rhd>\<^sub>1 B)\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M x \<rhd>\<^sub>1\<^sub>S Y"|
Fbox1_R:      "\<turnstile>d Z \<turnstile>\<^sub>F\<^sub>M a\<^sub>S\<^sub>A\<^sub>C \<rhd>\<^sub>1\<^sub>S B\<^sub>S\<^sub>F\<^sub>M \<Longrightarrow> \<turnstile>d Z \<turnstile>\<^sub>F\<^sub>M (a \<rhd>\<^sub>1 B)\<^sub>S\<^sub>F\<^sub>M"|
Bbox1_L:      "\<turnstile>d x \<turnstile>\<^sub>A\<^sub>C a\<^sub>S\<^sub>A\<^sub>C \<Longrightarrow> \<turnstile>d B\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M Y \<Longrightarrow> \<turnstile>d (a \<unrhd>\<^sub>1 B)\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M x \<unrhd>\<^sub>1\<^sub>S Y"|
Bbox1_R:      "\<turnstile>d Z \<turnstile>\<^sub>F\<^sub>M a\<^sub>S\<^sub>A\<^sub>C \<unrhd>\<^sub>1\<^sub>S B\<^sub>S\<^sub>F\<^sub>M \<Longrightarrow> \<turnstile>d Z \<turnstile>\<^sub>F\<^sub>M (a \<unrhd>\<^sub>1 B)\<^sub>S\<^sub>F\<^sub>M"|
Fbox2_L:      "\<turnstile>d x \<turnstile>\<^sub>A\<^sub>G a\<^sub>S\<^sub>A\<^sub>G \<Longrightarrow> \<turnstile>d B\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M Y \<Longrightarrow> \<turnstile>d (a \<rhd>\<^sub>2 B)\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M x \<rhd>\<^sub>2\<^sub>S Y"|
Fbox2_R:      "\<turnstile>d Z \<turnstile>\<^sub>F\<^sub>M a\<^sub>S\<^sub>A\<^sub>G \<rhd>\<^sub>2\<^sub>S B\<^sub>S\<^sub>F\<^sub>M \<Longrightarrow> \<turnstile>d Z \<turnstile>\<^sub>F\<^sub>M (a \<rhd>\<^sub>2 B)\<^sub>S\<^sub>F\<^sub>M"|
Bbox2_L:      "\<turnstile>d x \<turnstile>\<^sub>A\<^sub>G a\<^sub>S\<^sub>A\<^sub>G \<Longrightarrow> \<turnstile>d B\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M Y \<Longrightarrow> \<turnstile>d (a \<unrhd>\<^sub>2 B)\<^sub>S\<^sub>F\<^sub>M \<turnstile>\<^sub>F\<^sub>M x \<unrhd>\<^sub>2\<^sub>S Y"|
Bbox2_R:      "\<turnstile>d Z \<turnstile>\<^sub>F\<^sub>M a\<^sub>S\<^sub>A\<^sub>G \<unrhd>\<^sub>2\<^sub>S B\<^sub>S\<^sub>F\<^sub>M \<Longrightarrow> \<turnstile>d Z \<turnstile>\<^sub>F\<^sub>M (a \<unrhd>\<^sub>2 B)\<^sub>S\<^sub>F\<^sub>M"|
(* Heterogeneous Display Postulates *)
DH_fdiam0_f:  "\<turnstile>d x \<triangle>\<^sub>0\<^sub>S Y \<turnstile>\<^sub>F\<^sub>M Z \<Longrightarrow> \<turnstile>d Y \<turnstile>\<^sub>F\<^sub>M x \<unrhd>\<^sub>0\<^sub>S Z"|
DH_fdiam0_b:  "\<turnstile>d Y \<turnstile>\<^sub>F\<^sub>M x \<unrhd>\<^sub>0\<^sub>S Z \<Longrightarrow> \<turnstile>d x \<triangle>\<^sub>0\<^sub>S Y \<turnstile>\<^sub>F\<^sub>M Z"|
DH_bdiam0_f:  "\<turnstile>d x \<triangleq>\<^sub>0\<^sub>S Y \<turnstile>\<^sub>F\<^sub>M Z \<Longrightarrow> \<turnstile>d Y \<turnstile>\<^sub>F\<^sub>M x \<rhd>\<^sub>0\<^sub>S Z"| 
DH_bdiam0_b:  "\<turnstile>d Y \<turnstile>\<^sub>F\<^sub>M x \<rhd>\<^sub>0\<^sub>S Z \<Longrightarrow> \<turnstile>d x \<triangleq>\<^sub>0\<^sub>S Y \<turnstile>\<^sub>F\<^sub>M Z"|
DH_fdiam1_f:  "\<turnstile>d x \<triangle>\<^sub>1\<^sub>S Y \<turnstile>\<^sub>F\<^sub>M Z \<Longrightarrow> \<turnstile>d Y \<turnstile>\<^sub>F\<^sub>M x \<unrhd>\<^sub>1\<^sub>S Z"|
DH_fdiam1_b:  "\<turnstile>d Y \<turnstile>\<^sub>F\<^sub>M x \<unrhd>\<^sub>1\<^sub>S Z \<Longrightarrow> \<turnstile>d x \<triangle>\<^sub>1\<^sub>S Y \<turnstile>\<^sub>F\<^sub>M Z"|
DH_bdiam1_f:  "\<turnstile>d x \<triangleq>\<^sub>1\<^sub>S Y \<turnstile>\<^sub>F\<^sub>M Z \<Longrightarrow> \<turnstile>d Y \<turnstile>\<^sub>F\<^sub>M x \<rhd>\<^sub>1\<^sub>S Z"| 
DH_bdiam1_b:  "\<turnstile>d Y \<turnstile>\<^sub>F\<^sub>M x \<rhd>\<^sub>1\<^sub>S Z \<Longrightarrow> \<turnstile>d x \<triangleq>\<^sub>1\<^sub>S Y \<turnstile>\<^sub>F\<^sub>M Z"|
DH_fdiam2_f:  "\<turnstile>d x \<triangle>\<^sub>2\<^sub>S Y \<turnstile>\<^sub>F\<^sub>M Z \<Longrightarrow> \<turnstile>d Y \<turnstile>\<^sub>F\<^sub>M x \<unrhd>\<^sub>2\<^sub>S Z"|
DH_fdiam2_b:  "\<turnstile>d Y \<turnstile>\<^sub>F\<^sub>M x \<unrhd>\<^sub>2\<^sub>S Z \<Longrightarrow> \<turnstile>d x \<triangle>\<^sub>2\<^sub>S Y \<turnstile>\<^sub>F\<^sub>M Z"|
DH_bdiam2_f:  "\<turnstile>d x \<triangleq>\<^sub>2\<^sub>S Y \<turnstile>\<^sub>F\<^sub>M Z \<Longrightarrow> \<turnstile>d Y \<turnstile>\<^sub>F\<^sub>M x \<rhd>\<^sub>2\<^sub>S Z"| 
DH_bdiam2_b:  "\<turnstile>d Y \<turnstile>\<^sub>F\<^sub>M x \<rhd>\<^sub>2\<^sub>S Z \<Longrightarrow> \<turnstile>d x \<triangleq>\<^sub>2\<^sub>S Y \<turnstile>\<^sub>F\<^sub>M Z"|
DH_bla1_f:    "\<turnstile>d x \<turnstile>\<^sub>A\<^sub>C Z \<unlhd>\<^sub>1\<^sub>S Y \<Longrightarrow> \<turnstile>d x \<triangle>\<^sub>1\<^sub>S Y \<turnstile>\<^sub>F\<^sub>M Z"| 
DH_bla1_b:    "\<turnstile>d x \<triangle>\<^sub>1\<^sub>S Y \<turnstile>\<^sub>F\<^sub>M Z \<Longrightarrow> \<turnstile>d x \<turnstile>\<^sub>A\<^sub>C Z \<unlhd>\<^sub>1\<^sub>S Y"|
DH_wla1_f:    "\<turnstile>d x \<turnstile>\<^sub>A\<^sub>C Z \<lhd>\<^sub>1\<^sub>S Y \<Longrightarrow> \<turnstile>d x \<triangleq>\<^sub>1\<^sub>S Y \<turnstile>\<^sub>F\<^sub>M Z"| 
DH_wla1_b:    "\<turnstile>d x \<triangleq>\<^sub>1\<^sub>S Y \<turnstile>\<^sub>F\<^sub>M Z \<Longrightarrow> \<turnstile>d x \<turnstile>\<^sub>A\<^sub>C Z \<lhd>\<^sub>1\<^sub>S Y"|
DH_blas0_f:   "\<turnstile>d x \<turnstile>\<^sub>F\<^sub>A Z \<unlhd>~\<^sub>0\<^sub>S Y \<Longrightarrow> \<turnstile>d x \<triangle>\<^sub>0\<^sub>S Y \<turnstile>\<^sub>F\<^sub>M Z"| 
DH_blas0_b:   "\<turnstile>d x \<triangle>\<^sub>0\<^sub>S Y \<turnstile>\<^sub>F\<^sub>M Z \<Longrightarrow> \<turnstile>d x \<turnstile>\<^sub>F\<^sub>A Z \<unlhd>~\<^sub>0\<^sub>S Y"|
DH_wlas0_f:   "\<turnstile>d x \<turnstile>\<^sub>F\<^sub>A Z \<lhd>~\<^sub>0\<^sub>S Y \<Longrightarrow> \<turnstile>d x \<triangleq>\<^sub>0\<^sub>S Y \<turnstile>\<^sub>F\<^sub>M Z"| 
DH_wlas0_b:   "\<turnstile>d x \<triangleq>\<^sub>0\<^sub>S Y \<turnstile>\<^sub>F\<^sub>M Z \<Longrightarrow> \<turnstile>d x \<turnstile>\<^sub>F\<^sub>A Z \<lhd>~\<^sub>0\<^sub>S Y"|
DH_blas2_f:   "\<turnstile>d x \<turnstile>\<^sub>A\<^sub>G Z \<unlhd>~\<^sub>2\<^sub>S Y \<Longrightarrow> \<turnstile>d x \<triangle>\<^sub>2\<^sub>S Y \<turnstile>\<^sub>F\<^sub>M Z"| 
DH_blas2_b:   "\<turnstile>d x \<triangle>\<^sub>2\<^sub>S Y \<turnstile>\<^sub>F\<^sub>M Z \<Longrightarrow> \<turnstile>d x \<turnstile>\<^sub>A\<^sub>G Z \<unlhd>~\<^sub>2\<^sub>S Y"|
DH_wlas2_f:   "\<turnstile>d x \<turnstile>\<^sub>A\<^sub>G Z \<lhd>~\<^sub>2\<^sub>S Y \<Longrightarrow> \<turnstile>d x \<triangleq>\<^sub>2\<^sub>S Y \<turnstile>\<^sub>F\<^sub>M Z"| 
DH_wlas2_b:   "\<turnstile>d x \<triangleq>\<^sub>2\<^sub>S Y \<turnstile>\<^sub>F\<^sub>M Z \<Longrightarrow> \<turnstile>d x \<turnstile>\<^sub>A\<^sub>G Z \<lhd>~\<^sub>2\<^sub>S Y"|
DH_blas3_f:   "\<turnstile>d x \<turnstile>\<^sub>A\<^sub>G z \<unlhd>~\<^sub>3\<^sub>S y \<Longrightarrow> \<turnstile>d x \<triangle>\<^sub>3\<^sub>S y \<turnstile>\<^sub>A\<^sub>C z"| 
DH_blas3_b:   "\<turnstile>d x \<triangle>\<^sub>3\<^sub>S y \<turnstile>\<^sub>A\<^sub>C z \<Longrightarrow> \<turnstile>d x \<turnstile>\<^sub>A\<^sub>G z \<unlhd>~\<^sub>3\<^sub>S y"|
DH_wlas3_f:   "\<turnstile>d x \<turnstile>\<^sub>A\<^sub>G z \<lhd>~\<^sub>3\<^sub>S y \<Longrightarrow> \<turnstile>d x \<triangleq>\<^sub>3\<^sub>S y \<turnstile>\<^sub>A\<^sub>C z"| 
DH_wlas3_b:   "\<turnstile>d x \<triangleq>\<^sub>3\<^sub>S y \<turnstile>\<^sub>A\<^sub>C z \<Longrightarrow> \<turnstile>d x \<turnstile>\<^sub>A\<^sub>G z \<lhd>~\<^sub>3\<^sub>S y"|
DH_fdiam3_f:  "\<turnstile>d x \<triangle>\<^sub>3\<^sub>S y \<turnstile>\<^sub>A\<^sub>C z \<Longrightarrow> \<turnstile>d y \<turnstile>\<^sub>F\<^sub>A x ~\<unrhd>\<^sub>3\<^sub>S z"|
DH_fdiam3_b:  "\<turnstile>d y \<turnstile>\<^sub>F\<^sub>A x ~\<unrhd>\<^sub>3\<^sub>S z \<Longrightarrow> \<turnstile>d x \<triangle>\<^sub>3\<^sub>S y \<turnstile>\<^sub>A\<^sub>C z"|
DH_bdiam3_f:  "\<turnstile>d x \<triangleq>\<^sub>3\<^sub>S y \<turnstile>\<^sub>A\<^sub>C z \<Longrightarrow> \<turnstile>d y \<turnstile>\<^sub>F\<^sub>A x ~\<rhd>\<^sub>3\<^sub>S z"| 
DH_bdiam3_b:  "\<turnstile>d y \<turnstile>\<^sub>F\<^sub>A x ~\<rhd>\<^sub>3\<^sub>S z \<Longrightarrow> \<turnstile>d x \<triangleq>\<^sub>3\<^sub>S y \<turnstile>\<^sub>A\<^sub>C z"|
(* Heterogeneous Structural Rules *)
Nec_fdiam0:   "\<turnstile>d I\<^sub>S \<turnstile>\<^sub>F\<^sub>M W \<Longrightarrow> \<turnstile>d  x \<triangle>\<^sub>0\<^sub>S I\<^sub>S \<turnstile>\<^sub>F\<^sub>M W"|
Nec_fbox0:    "\<turnstile>d W \<turnstile>\<^sub>F\<^sub>M I\<^sub>S  \<Longrightarrow> \<turnstile>d W  \<turnstile>\<^sub>F\<^sub>M x \<rhd>\<^sub>0\<^sub>S I\<^sub>S"|
Nec_bdiam0:   "\<turnstile>d I\<^sub>S \<turnstile>\<^sub>F\<^sub>M W \<Longrightarrow> \<turnstile>d  x \<triangleq>\<^sub>0\<^sub>S I\<^sub>S \<turnstile>\<^sub>F\<^sub>M W"|
Nec_bbox0:    "\<turnstile>d W \<turnstile>\<^sub>F\<^sub>M I\<^sub>S \<Longrightarrow> \<turnstile>d W  \<turnstile>\<^sub>F\<^sub>M x \<unrhd>\<^sub>0\<^sub>S I\<^sub>S"|
Conj_fdiam0:  "\<turnstile>d x \<triangle>\<^sub>0\<^sub>S ((x \<triangleq>\<^sub>0\<^sub>S Y) ;\<^sub>S Z) \<turnstile>\<^sub>F\<^sub>M W \<Longrightarrow> \<turnstile>d Y ;\<^sub>S (x \<triangle>\<^sub>0\<^sub>S Z) \<turnstile>\<^sub>F\<^sub>M W"|
Conj_fbox0:   "\<turnstile>d W \<turnstile>\<^sub>F\<^sub>M x \<rhd>\<^sub>0\<^sub>S ((x \<unrhd>\<^sub>0\<^sub>S Y) ;\<^sub>S Z) \<Longrightarrow> \<turnstile>d W  \<turnstile>\<^sub>F\<^sub>M Y ;\<^sub>S (x \<rhd>\<^sub>0\<^sub>S Z)"|
Conj_bdiam0:  "\<turnstile>d x \<triangleq>\<^sub>0\<^sub>S ((x \<triangle>\<^sub>0\<^sub>S Y) ;\<^sub>S Z) \<turnstile>\<^sub>F\<^sub>M W \<Longrightarrow> \<turnstile>d Y ;\<^sub>S (x \<triangleq>\<^sub>0\<^sub>S Z) \<turnstile>\<^sub>F\<^sub>M W"|
Conj_bbox0:   "\<turnstile>d W \<turnstile>\<^sub>F\<^sub>M x \<unrhd>\<^sub>0\<^sub>S ((x \<rhd>\<^sub>0\<^sub>S Y) ;\<^sub>S Z) \<Longrightarrow> \<turnstile>d W  \<turnstile>\<^sub>F\<^sub>M Y ;\<^sub>S (x \<unrhd>\<^sub>0\<^sub>S Z)"|
FS_fdiam0:    "\<turnstile>d (x \<rhd>\<^sub>0\<^sub>S Y) \<rightarrow>\<^sub>S (x \<triangle>\<^sub>0\<^sub>S Z) \<turnstile>\<^sub>F\<^sub>M W \<Longrightarrow> \<turnstile>d x \<triangle>\<^sub>0\<^sub>S (Y \<rightarrow>\<^sub>S Z) \<turnstile>\<^sub>F\<^sub>M W"|
FS_fbox0:     "\<turnstile>d W \<turnstile>\<^sub>F\<^sub>M (x \<triangle>\<^sub>0\<^sub>S Y) \<rightarrow>\<^sub>S (x \<rhd>\<^sub>0\<^sub>S Z) \<Longrightarrow> \<turnstile>d W  \<turnstile>\<^sub>F\<^sub>M x \<rhd>\<^sub>0\<^sub>S (Y \<rightarrow>\<^sub>S Z)"|
FS_bdiam0:    "\<turnstile>d (x \<unrhd>\<^sub>0\<^sub>S Y) \<rightarrow>\<^sub>S (x \<triangleq>\<^sub>0\<^sub>S Z) \<turnstile>\<^sub>F\<^sub>M W \<Longrightarrow> \<turnstile>d x \<triangleq>\<^sub>0\<^sub>S (Y \<rightarrow>\<^sub>S Z) \<turnstile>\<^sub>F\<^sub>M W"|
FS_bbox0:     "\<turnstile>d W \<turnstile>\<^sub>F\<^sub>M (x \<triangleq>\<^sub>0\<^sub>S Y) \<rightarrow>\<^sub>S (x \<unrhd>\<^sub>0\<^sub>S Z) \<Longrightarrow> \<turnstile>d W  \<turnstile>\<^sub>F\<^sub>M x \<unrhd>\<^sub>0\<^sub>S (Y \<rightarrow>\<^sub>S Z)"|
Mon_fdiam0:   "\<turnstile>d (x \<triangle>\<^sub>0\<^sub>S Y) ;\<^sub>S (x \<triangle>\<^sub>0\<^sub>S Z) \<turnstile>\<^sub>F\<^sub>M W \<Longrightarrow> \<turnstile>d x \<triangle>\<^sub>0\<^sub>S (Y ;\<^sub>S Z) \<turnstile>\<^sub>F\<^sub>M W"|
Mon_fbox0:    "\<turnstile>d W \<turnstile>\<^sub>F\<^sub>M (x \<rhd>\<^sub>0\<^sub>S Y) ;\<^sub>S (x \<rhd>\<^sub>0\<^sub>S Z)  \<Longrightarrow> \<turnstile>d W  \<turnstile>\<^sub>F\<^sub>M x \<rhd>\<^sub>0\<^sub>S (Y ;\<^sub>S Z)"|
Mon_bdiam0:   "\<turnstile>d (x \<triangleq>\<^sub>0\<^sub>S Y) ;\<^sub>S (x \<triangleq>\<^sub>0\<^sub>S Z) \<turnstile>\<^sub>F\<^sub>M W \<Longrightarrow> \<turnstile>d x \<triangleq>\<^sub>0\<^sub>S (Y ;\<^sub>S Z) \<turnstile>\<^sub>F\<^sub>M W"|
Mon_bbox0:    "\<turnstile>d W \<turnstile>\<^sub>F\<^sub>M (x \<unrhd>\<^sub>0\<^sub>S Y) ;\<^sub>S (x \<unrhd>\<^sub>0\<^sub>S Z)  \<Longrightarrow> \<turnstile>d W  \<turnstile>\<^sub>F\<^sub>M x \<unrhd>\<^sub>0\<^sub>S (Y ;\<^sub>S Z)"|
Nec_fdiam1:   "\<turnstile>d I\<^sub>S \<turnstile>\<^sub>F\<^sub>M W \<Longrightarrow> \<turnstile>d  x \<triangle>\<^sub>1\<^sub>S I\<^sub>S \<turnstile>\<^sub>F\<^sub>M W"|
Nec_fbox1:    "\<turnstile>d W \<turnstile>\<^sub>F\<^sub>M I\<^sub>S  \<Longrightarrow> \<turnstile>d W  \<turnstile>\<^sub>F\<^sub>M x \<rhd>\<^sub>1\<^sub>S I\<^sub>S"|
Nec_bdiam1:   "\<turnstile>d I\<^sub>S \<turnstile>\<^sub>F\<^sub>M W \<Longrightarrow> \<turnstile>d  x \<triangleq>\<^sub>1\<^sub>S I\<^sub>S \<turnstile>\<^sub>F\<^sub>M W"|
Nec_bbox1:    "\<turnstile>d W \<turnstile>\<^sub>F\<^sub>M I\<^sub>S \<Longrightarrow> \<turnstile>d W  \<turnstile>\<^sub>F\<^sub>M x \<unrhd>\<^sub>1\<^sub>S I\<^sub>S"|
Conj_fdiam1:  "\<turnstile>d x \<triangle>\<^sub>1\<^sub>S ((x \<triangleq>\<^sub>1\<^sub>S Y) ;\<^sub>S Z) \<turnstile>\<^sub>F\<^sub>M W \<Longrightarrow> \<turnstile>d Y ;\<^sub>S (x \<triangle>\<^sub>1\<^sub>S Z) \<turnstile>\<^sub>F\<^sub>M W"|
Conj_fbox1:   "\<turnstile>d W \<turnstile>\<^sub>F\<^sub>M x \<rhd>\<^sub>1\<^sub>S ((x \<unrhd>\<^sub>1\<^sub>S Y) ;\<^sub>S Z) \<Longrightarrow> \<turnstile>d W  \<turnstile>\<^sub>F\<^sub>M Y ;\<^sub>S (x \<rhd>\<^sub>1\<^sub>S Z)"|
Conj_bdiam1:  "\<turnstile>d x \<triangleq>\<^sub>1\<^sub>S ((x \<triangle>\<^sub>1\<^sub>S Y) ;\<^sub>S Z) \<turnstile>\<^sub>F\<^sub>M W \<Longrightarrow> \<turnstile>d Y ;\<^sub>S (x \<triangleq>\<^sub>1\<^sub>S Z) \<turnstile>\<^sub>F\<^sub>M W"|
Conj_bbox1:   "\<turnstile>d W \<turnstile>\<^sub>F\<^sub>M x \<unrhd>\<^sub>1\<^sub>S ((x \<rhd>\<^sub>1\<^sub>S Y) ;\<^sub>S Z) \<Longrightarrow> \<turnstile>d W  \<turnstile>\<^sub>F\<^sub>M Y ;\<^sub>S (x \<unrhd>\<^sub>1\<^sub>S Z)"|
FS_fdiam1:    "\<turnstile>d (x \<rhd>\<^sub>1\<^sub>S Y) \<rightarrow>\<^sub>S (x \<triangle>\<^sub>1\<^sub>S Z) \<turnstile>\<^sub>F\<^sub>M W \<Longrightarrow> \<turnstile>d x \<triangle>\<^sub>1\<^sub>S (Y \<rightarrow>\<^sub>S Z) \<turnstile>\<^sub>F\<^sub>M W"|
FS_fbox1:     "\<turnstile>d W \<turnstile>\<^sub>F\<^sub>M (x \<triangle>\<^sub>1\<^sub>S Y) \<rightarrow>\<^sub>S (x \<rhd>\<^sub>1\<^sub>S Z) \<Longrightarrow> \<turnstile>d W  \<turnstile>\<^sub>F\<^sub>M x \<rhd>\<^sub>1\<^sub>S (Y \<rightarrow>\<^sub>S Z)"|
FS_bdiam1:    "\<turnstile>d (x \<unrhd>\<^sub>1\<^sub>S Y) \<rightarrow>\<^sub>S (x \<triangleq>\<^sub>1\<^sub>S Z) \<turnstile>\<^sub>F\<^sub>M W \<Longrightarrow> \<turnstile>d x \<triangleq>\<^sub>1\<^sub>S (Y \<rightarrow>\<^sub>S Z) \<turnstile>\<^sub>F\<^sub>M W"|
FS_bbox1:     "\<turnstile>d W \<turnstile>\<^sub>F\<^sub>M (x \<triangleq>\<^sub>1\<^sub>S Y) \<rightarrow>\<^sub>S (x \<unrhd>\<^sub>1\<^sub>S Z) \<Longrightarrow> \<turnstile>d W  \<turnstile>\<^sub>F\<^sub>M x \<unrhd>\<^sub>1\<^sub>S (Y \<rightarrow>\<^sub>S Z)"|
Mon_fdiam1:   "\<turnstile>d (x \<triangle>\<^sub>1\<^sub>S Y) ;\<^sub>S (x \<triangle>\<^sub>1\<^sub>S Z) \<turnstile>\<^sub>F\<^sub>M W \<Longrightarrow> \<turnstile>d x \<triangle>\<^sub>1\<^sub>S (Y ;\<^sub>S Z) \<turnstile>\<^sub>F\<^sub>M W"|
Mon_fbox1:    "\<turnstile>d W \<turnstile>\<^sub>F\<^sub>M (x \<rhd>\<^sub>1\<^sub>S Y) ;\<^sub>S (x \<rhd>\<^sub>1\<^sub>S Z)  \<Longrightarrow> \<turnstile>d W  \<turnstile>\<^sub>F\<^sub>M x \<rhd>\<^sub>1\<^sub>S (Y ;\<^sub>S Z)"|
Mon_bdiam1:   "\<turnstile>d (x \<triangleq>\<^sub>1\<^sub>S Y) ;\<^sub>S (x \<triangleq>\<^sub>1\<^sub>S Z) \<turnstile>\<^sub>F\<^sub>M W \<Longrightarrow> \<turnstile>d x \<triangleq>\<^sub>1\<^sub>S (Y ;\<^sub>S Z) \<turnstile>\<^sub>F\<^sub>M W"|
Mon_bbox1:    "\<turnstile>d W \<turnstile>\<^sub>F\<^sub>M (x \<unrhd>\<^sub>1\<^sub>S Y) ;\<^sub>S (x \<unrhd>\<^sub>1\<^sub>S Z)  \<Longrightarrow> \<turnstile>d W  \<turnstile>\<^sub>F\<^sub>M x \<unrhd>\<^sub>1\<^sub>S (Y ;\<^sub>S Z)"|
Nec_fdiam2:   "\<turnstile>d I\<^sub>S \<turnstile>\<^sub>F\<^sub>M W \<Longrightarrow> \<turnstile>d  x \<triangle>\<^sub>2\<^sub>S I\<^sub>S \<turnstile>\<^sub>F\<^sub>M W"|
Nec_fbox2:    "\<turnstile>d W \<turnstile>\<^sub>F\<^sub>M I\<^sub>S  \<Longrightarrow> \<turnstile>d W  \<turnstile>\<^sub>F\<^sub>M x \<rhd>\<^sub>2\<^sub>S I\<^sub>S"|
Nec_bdiam2:   "\<turnstile>d I\<^sub>S \<turnstile>\<^sub>F\<^sub>M W \<Longrightarrow> \<turnstile>d  x \<triangleq>\<^sub>2\<^sub>S I\<^sub>S \<turnstile>\<^sub>F\<^sub>M W"|
Nec_bbox2:    "\<turnstile>d W \<turnstile>\<^sub>F\<^sub>M I\<^sub>S \<Longrightarrow> \<turnstile>d W  \<turnstile>\<^sub>F\<^sub>M x \<unrhd>\<^sub>2\<^sub>S I\<^sub>S"|
Conj_fdiam2:  "\<turnstile>d x \<triangle>\<^sub>2\<^sub>S ((x \<triangleq>\<^sub>2\<^sub>S Y) ;\<^sub>S Z) \<turnstile>\<^sub>F\<^sub>M W \<Longrightarrow> \<turnstile>d Y ;\<^sub>S (x \<triangle>\<^sub>2\<^sub>S Z) \<turnstile>\<^sub>F\<^sub>M W"|
Conj_fbox2:   "\<turnstile>d W \<turnstile>\<^sub>F\<^sub>M x \<rhd>\<^sub>2\<^sub>S ((x \<unrhd>\<^sub>2\<^sub>S Y) ;\<^sub>S Z) \<Longrightarrow> \<turnstile>d W  \<turnstile>\<^sub>F\<^sub>M Y ;\<^sub>S (x \<rhd>\<^sub>2\<^sub>S Z)"|
Conj_bdiam2:  "\<turnstile>d x \<triangleq>\<^sub>2\<^sub>S ((x \<triangle>\<^sub>2\<^sub>S Y) ;\<^sub>S Z) \<turnstile>\<^sub>F\<^sub>M W \<Longrightarrow> \<turnstile>d Y ;\<^sub>S (x \<triangleq>\<^sub>2\<^sub>S Z) \<turnstile>\<^sub>F\<^sub>M W"|
Conj_bbox2:   "\<turnstile>d W \<turnstile>\<^sub>F\<^sub>M x \<unrhd>\<^sub>2\<^sub>S ((x \<rhd>\<^sub>2\<^sub>S Y) ;\<^sub>S Z) \<Longrightarrow> \<turnstile>d W  \<turnstile>\<^sub>F\<^sub>M Y ;\<^sub>S (x \<unrhd>\<^sub>2\<^sub>S Z)"|
FS_fdiam2:    "\<turnstile>d (x \<rhd>\<^sub>2\<^sub>S Y) \<rightarrow>\<^sub>S (x \<triangle>\<^sub>2\<^sub>S Z) \<turnstile>\<^sub>F\<^sub>M W \<Longrightarrow> \<turnstile>d x \<triangle>\<^sub>2\<^sub>S (Y \<rightarrow>\<^sub>S Z) \<turnstile>\<^sub>F\<^sub>M W"|
FS_fbox2:     "\<turnstile>d W \<turnstile>\<^sub>F\<^sub>M (x \<triangle>\<^sub>2\<^sub>S Y) \<rightarrow>\<^sub>S (x \<rhd>\<^sub>2\<^sub>S Z) \<Longrightarrow> \<turnstile>d W  \<turnstile>\<^sub>F\<^sub>M x \<rhd>\<^sub>2\<^sub>S (Y \<rightarrow>\<^sub>S Z)"|
FS_bdiam2:    "\<turnstile>d (x \<unrhd>\<^sub>2\<^sub>S Y) \<rightarrow>\<^sub>S (x \<triangleq>\<^sub>2\<^sub>S Z) \<turnstile>\<^sub>F\<^sub>M W \<Longrightarrow> \<turnstile>d x \<triangleq>\<^sub>2\<^sub>S (Y \<rightarrow>\<^sub>S Z) \<turnstile>\<^sub>F\<^sub>M W"|
FS_bbox2:     "\<turnstile>d W \<turnstile>\<^sub>F\<^sub>M (x \<triangleq>\<^sub>2\<^sub>S Y) \<rightarrow>\<^sub>S (x \<unrhd>\<^sub>2\<^sub>S Z) \<Longrightarrow> \<turnstile>d W  \<turnstile>\<^sub>F\<^sub>M x \<unrhd>\<^sub>2\<^sub>S (Y \<rightarrow>\<^sub>S Z)"|
Mon_fdiam2:   "\<turnstile>d (x \<triangle>\<^sub>2\<^sub>S Y) ;\<^sub>S (x \<triangle>\<^sub>2\<^sub>S Z) \<turnstile>\<^sub>F\<^sub>M W \<Longrightarrow> \<turnstile>d x \<triangle>\<^sub>2\<^sub>S (Y ;\<^sub>S Z) \<turnstile>\<^sub>F\<^sub>M W"|
Mon_fbox2:    "\<turnstile>d W \<turnstile>\<^sub>F\<^sub>M (x \<rhd>\<^sub>2\<^sub>S Y) ;\<^sub>S (x \<rhd>\<^sub>2\<^sub>S Z)  \<Longrightarrow> \<turnstile>d W  \<turnstile>\<^sub>F\<^sub>M x \<rhd>\<^sub>2\<^sub>S (Y ;\<^sub>S Z)"|
Mon_bdiam2:   "\<turnstile>d (x \<triangleq>\<^sub>2\<^sub>S Y) ;\<^sub>S (x \<triangleq>\<^sub>2\<^sub>S Z) \<turnstile>\<^sub>F\<^sub>M W \<Longrightarrow> \<turnstile>d x \<triangleq>\<^sub>2\<^sub>S (Y ;\<^sub>S Z) \<turnstile>\<^sub>F\<^sub>M W"|
Mon_bbox2:    "\<turnstile>d W \<turnstile>\<^sub>F\<^sub>M (x \<unrhd>\<^sub>2\<^sub>S Y) ;\<^sub>S (x \<unrhd>\<^sub>2\<^sub>S Z) \<Longrightarrow> \<turnstile>d W \<turnstile>\<^sub>F\<^sub>M x \<unrhd>\<^sub>2\<^sub>S (Y ;\<^sub>S Z)"|
(* Interaction Rules *)
Swapout_L:    "\<turnstile>d (a \<triangleq>\<^sub>3\<^sub>S F) \<triangleq>\<^sub>1\<^sub>S (a \<triangleq>\<^sub>2\<^sub>S X) \<turnstile>\<^sub>F\<^sub>M Y \<Longrightarrow> \<turnstile>d a \<triangleq>\<^sub>2\<^sub>S (F \<triangleq>\<^sub>0\<^sub>S X) \<turnstile>\<^sub>F\<^sub>M Y"|
Swapout_R:    "\<turnstile>d X \<turnstile>\<^sub>F\<^sub>M (a \<triangleq>\<^sub>3\<^sub>S F) \<unrhd>\<^sub>1\<^sub>S (a \<unrhd>\<^sub>2\<^sub>S Y) \<Longrightarrow> \<turnstile>d X \<turnstile>\<^sub>F\<^sub>M a \<unrhd>\<^sub>2\<^sub>S (F \<unrhd>\<^sub>0\<^sub>S Y)"|
Swapin_L:     "\<turnstile>d  a \<triangleq>\<^sub>2\<^sub>S (F \<triangleq>\<^sub>0\<^sub>S X) \<turnstile>\<^sub>F\<^sub>M Y \<Longrightarrow> \<turnstile>d (a \<triangleq>\<^sub>3\<^sub>S F) \<triangleq>\<^sub>1\<^sub>S (a \<triangleq>\<^sub>2\<^sub>S ((F \<triangle>\<^sub>0\<^sub>S I\<^sub>S) ;\<^sub>S X)) \<turnstile>\<^sub>F\<^sub>M Y"|
Swapin_R:     "\<turnstile>d X \<turnstile>\<^sub>F\<^sub>M a \<unrhd>\<^sub>2\<^sub>S (F \<unrhd>\<^sub>0\<^sub>S Y) \<Longrightarrow> \<turnstile>d X \<turnstile>\<^sub>F\<^sub>M (a \<triangleq>\<^sub>3\<^sub>S F) \<unrhd>\<^sub>1\<^sub>S (a \<unrhd>\<^sub>2\<^sub>S ((F \<triangle>\<^sub>0\<^sub>S I\<^sub>S) \<rightarrow>\<^sub>S Y))"|
(* Atom *)
Atom:         "atom seq \<Longrightarrow> \<turnstile>d seq"| 
(* Balance Rule *)
Balance:      "\<turnstile>d X \<turnstile>\<^sub>F\<^sub>M Y \<Longrightarrow> \<turnstile>d F \<triangle>\<^sub>0\<^sub>S X  \<turnstile>\<^sub>F\<^sub>M F \<rhd>\<^sub>0\<^sub>S Y"


end

