theory MDEAK_method
imports Main "~~/src/HOL/Eisbach/Eisbach_Tools"  MDEAK_Core_SE MDEAK_SE
begin

method mdeak = (simp_all only: Id_fm Id_ag Id_fa Cut_fm Cut_ag Cut_ac Cut_fa I_1L_f I_1L_b I_1R_f I_1R_b I_2L_f I_2L_b I_2R_f I_2R_b IW_L IW_R W_1L W_1R W_2L W_2R C_L C_R E_L E_R A_L A_R D_IL1_f D_IL1_b D_IL2_f D_IL2_b D_IR1_f D_IR1_b D_IR2_f D_IR2_b Gr_L_f Gr_L_b Gr_R_f Gr_R_b Bot_L Bot_R Top_L Top_R And_L And_R Or_L Or_R ImpL_L ImpL_R DimpL_L DimpL_R ImpR_L ImpR_R DimpR_L DimpR_R Fdiam0_L Fdiam0_R Bdiam0_L Bdiam0_R Fdiam1_L Fdiam1_R Bdiam1_L Bdiam1_R Fdiam2_L Fdiam2_R Bdiam2_L Bdiam2_R Fdiam3_L Fdiam3_R Bdiam3_L Bdiam3_R Fbox0_L Fbox0_R Bbox0_L Bbox0_R Fbox1_L Fbox1_R Bbox1_L Bbox1_R Fbox2_L Fbox2_R Bbox2_L Bbox2_R DH_fdiam0_f DH_fdiam0_b DH_bdiam0_f DH_bdiam0_b DH_fdiam1_f DH_fdiam1_b DH_bdiam1_f DH_bdiam1_b DH_fdiam2_f DH_fdiam2_b DH_bdiam2_f DH_bdiam2_b DH_bla1_f DH_bla1_b DH_wla1_f DH_wla1_b DH_blas0_f DH_blas0_b DH_wlas0_f DH_wlas0_b DH_blas2_f DH_blas2_b DH_wlas2_f DH_wlas2_b DH_blas3_f DH_blas3_b DH_wlas3_f DH_wlas3_b DH_fdiam3_f DH_fdiam3_b DH_bdiam3_f DH_bdiam3_b Nec_fdiam0 Nec_fbox0 Nec_bdiam0 Nec_bbox0 Conj_fdiam0 Conj_fbox0 Conj_bdiam0 Conj_bbox0 FS_fdiam0 FS_fbox0 FS_bdiam0 FS_bbox0 Mon_fdiam0 Mon_fbox0 Mon_bdiam0 Mon_bbox0 Nec_fdiam1 Nec_fbox1 Nec_bdiam1 Nec_bbox1 Conj_fdiam1 Conj_fbox1 Conj_bdiam1 Conj_bbox1 FS_fdiam1 FS_fbox1 FS_bdiam1 FS_bbox1 Mon_fdiam1 Mon_fbox1 Mon_bdiam1 Mon_bbox1 Nec_fdiam2 Nec_fbox2 Nec_bdiam2 Nec_bbox2 Conj_fdiam2 Conj_fbox2 Conj_bdiam2 Conj_bbox2 FS_fdiam2 FS_fbox2 FS_bdiam2 FS_bbox2 Mon_fdiam2 Mon_fbox2 Mon_bdiam2 Mon_bbox2 Swapout_L Swapout_R Swapin_L Swapin_R Atom Balance)
method mdeak_b = (blast intro: Id_fm Id_ag Id_fa Cut_fm Cut_ag Cut_ac Cut_fa I_1L_f I_1L_b I_1R_f I_1R_b I_2L_f I_2L_b I_2R_f I_2R_b IW_L IW_R W_1L W_1R W_2L W_2R C_L C_R E_L E_R A_L A_R D_IL1_f D_IL1_b D_IL2_f D_IL2_b D_IR1_f D_IR1_b D_IR2_f D_IR2_b Gr_L_f Gr_L_b Gr_R_f Gr_R_b Bot_L Bot_R Top_L Top_R And_L And_R Or_L Or_R ImpL_L ImpL_R DimpL_L DimpL_R ImpR_L ImpR_R DimpR_L DimpR_R Fdiam0_L Fdiam0_R Bdiam0_L Bdiam0_R Fdiam1_L Fdiam1_R Bdiam1_L Bdiam1_R Fdiam2_L Fdiam2_R Bdiam2_L Bdiam2_R Fdiam3_L Fdiam3_R Bdiam3_L Bdiam3_R Fbox0_L Fbox0_R Bbox0_L Bbox0_R Fbox1_L Fbox1_R Bbox1_L Bbox1_R Fbox2_L Fbox2_R Bbox2_L Bbox2_R DH_fdiam0_f DH_fdiam0_b DH_bdiam0_f DH_bdiam0_b DH_fdiam1_f DH_fdiam1_b DH_bdiam1_f DH_bdiam1_b DH_fdiam2_f DH_fdiam2_b DH_bdiam2_f DH_bdiam2_b DH_bla1_f DH_bla1_b DH_wla1_f DH_wla1_b DH_blas0_f DH_blas0_b DH_wlas0_f DH_wlas0_b DH_blas2_f DH_blas2_b DH_wlas2_f DH_wlas2_b DH_blas3_f DH_blas3_b DH_wlas3_f DH_wlas3_b DH_fdiam3_f DH_fdiam3_b DH_bdiam3_f DH_bdiam3_b Nec_fdiam0 Nec_fbox0 Nec_bdiam0 Nec_bbox0 Conj_fdiam0 Conj_fbox0 Conj_bdiam0 Conj_bbox0 FS_fdiam0 FS_fbox0 FS_bdiam0 FS_bbox0 Mon_fdiam0 Mon_fbox0 Mon_bdiam0 Mon_bbox0 Nec_fdiam1 Nec_fbox1 Nec_bdiam1 Nec_bbox1 Conj_fdiam1 Conj_fbox1 Conj_bdiam1 Conj_bbox1 FS_fdiam1 FS_fbox1 FS_bdiam1 FS_bbox1 Mon_fdiam1 Mon_fbox1 Mon_bdiam1 Mon_bbox1 Nec_fdiam2 Nec_fbox2 Nec_bdiam2 Nec_bbox2 Conj_fdiam2 Conj_fbox2 Conj_bdiam2 Conj_bbox2 FS_fdiam2 FS_fbox2 FS_bdiam2 FS_bbox2 Mon_fdiam2 Mon_fbox2 Mon_bdiam2 Mon_bbox2 Swapout_L Swapout_R Swapin_L Swapin_R Atom Balance)

end