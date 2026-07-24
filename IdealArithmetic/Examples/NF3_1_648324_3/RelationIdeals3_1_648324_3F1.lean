import IdealArithmetic.Examples.NF3_1_648324_3.PrimesBelow3_1_648324_3F1
import IdealArithmetic.Examples.NF3_1_648324_3.ClassGroupData3_1_648324_3

set_option linter.all false

noncomputable section


noncomputable def E41RS0 : RelationCertificate Table 2 ![![41, 0, 0], ![9, 1, 0]]
  ![-5276102, -417675, 104455] ![![2, 0, 0], ![-53, -3, 1]] where
    su := ![![82, 0, 0], ![18, 2, 0]]
    hsu := by decide
    w := ![![-10552204, -835350, 208910], ![-31789634, 999756, 154688]]
    hw := by decide
    g := ![![![-2077808673, 46822858935, 12565517585], ![-8889598535, 0, 0]], ![![-1206940661, 27198082768, 7298956003], ![-5163717941, 0, 0]]]
    h := ![![![-57108790, -6771747, -93105], ![259576032, 1960880, 0]], ![![-171759074, -20327695, -286696], ![780691913, 5915940, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N0 : Ideal.span {2} * I41N0 =  Ideal.span {B.equivFun.symm ![-5276102, -417675, 104455]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E41RS0 


noncomputable def E41RS2 : RelationCertificate Table 2 ![![41, 0, 0], ![19, 1, 0]]
  ![229336, 88957, -14098] ![![2, 0, 0], ![-53, -4, 1]] where
    su := ![![82, 0, 0], ![38, 2, 0]]
    hsu := by decide
    w := ![![458672, 177914, -28196], ![49763866, 3138330, -877064]]
    hw := by decide
    g := ![![![238950454, -3858941221, -1146313597], ![812539451, 0, -11736]], ![![197088076, -3182791497, -945441594], ![670028955, 0, -5542]]]
    h := ![![![1061076, 70165, 966], ![-2277620, -26852, 0]], ![![114220352, 7403389, 135142], ![-245165921, -2989677, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N2 : Ideal.span {2} * I41N2 =  Ideal.span {B.equivFun.symm ![229336, 88957, -14098]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E41RS2 


noncomputable def E43RS1 : RelationCertificate Table 2 ![![43, 0, 0], ![-18, 1, 0]]
  ![-4672, -381, 94] ![![2, 0, 0], ![-53, -4, 1]] where
    su := ![![86, 0, 0], ![-36, 2, 0]]
    hsu := by decide
    w := ![![-9344, -762, 188], ![-74866, -2414, 1008]]
    hw := by decide
    g := ![![![19349, -100863, 14198], ![-303411, 0, 9576]], ![![-7239, 33902, -7278], ![120402, 0, -3762]]]
    h := ![![![-35536, 2159, -20], ![-84632, 477, 0]], ![![-285047, 17323, -162], ![-678866, 3735, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {2} * I43N1 =  Ideal.span {B.equivFun.symm ![-4672, -381, 94]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E43RS1 


noncomputable def E61RS1 : RelationCertificate Table 2 ![![61, 0, 0], ![20, 1, 0]]
  ![17240, 555, -232] ![![2, 0, 0], ![-53, -4, 1]] where
    su := ![![122, 0, 0], ![40, 2, 0]]
    hsu := by decide
    w := ![![34480, 1110, -464], ![-281962, -27668, 6304]]
    hw := by decide
    g := ![![![68788, -552452, -47562], ![-740485, 0, 25272]], ![![28482, -266166, -38723], ![-240550, 0, 8748]]]
    h := ![![![294480, 17977, 322], ![-897302, -9937, 0]], ![![-2411781, -147357, -2614], ![7348883, 81303, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {2} * I61N1 =  Ideal.span {B.equivFun.symm ![17240, 555, -232]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E61RS1 


noncomputable def E61RS2 : RelationCertificate Table 2 ![![61, 0, 0], ![-27, 1, 0]]
  ![-26, -7, -1] ![![2, 0, 0], ![-53, -3, 1]] where
    su := ![![122, 0, 0], ![-54, 2, 0]]
    hsu := by decide
    w := ![![-52, -14, -2], ![-326, -88, -12]]
    hw := by decide
    g := ![![![27, 1, -1], ![11, 0, 0]], ![![16, 1, 0], ![-5, 0, 0]]]
    h := ![![![-1400, 65, -1], ![-3162, 30, 0]], ![![-8968, 384, -4], ![-20255, 119, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N2 : Ideal.span {2} * I61N2 =  Ideal.span {B.equivFun.symm ![-26, -7, -1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E61RS2 


noncomputable def E67RS1 : RelationCertificate Table 2 ![![67, 0, 0], ![4, 1, 0]]
  ![4, 1, 0] ![![2, 0, 0], ![-53, -4, 1]] where
    su := ![![134, 0, 0], ![8, 2, 0]]
    hsu := by decide
    w := ![![8, 2, 0], ![214, 12, -4]]
    hw := by decide
    g := ![![![-46697, 212687, -50101], ![787995, 0, -24564]], ![![-3015, 13873, -3268], ![51392, 0, -1602]]]
    h := ![![![-4, -1, 0], ![68, 0, 0]], ![![101, 25, 0], ![-1665, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {2} * I67N1 =  Ideal.span {B.equivFun.symm ![4, 1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E67RS1 


noncomputable def E67RS2 : RelationCertificate Table 2 ![![67, 0, 0], ![-6, 1, 0]]
  ![25492, -5106, 457] ![![2, 0, 0], ![-53, -3, 1]] where
    su := ![![134, 0, 0], ![-12, 2, 0]]
    hsu := by decide
    w := ![![50984, -10212, 914], ![-4110278, -233154, 68924]]
    hw := by decide
    g := ![![![3016145, -67967454, -18239943], ![12904027, 0, 0]], ![![396906, -8943041, -2399982], ![1697892, 0, 0]]]
    h := ![![![289516, -48632, 129], ![3228680, -4093, 0]], ![![-23324191, 3910520, -9488], ![-260110943, 335079, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N2 : Ideal.span {2} * I67N2 =  Ideal.span {B.equivFun.symm ![25492, -5106, 457]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E67RS2 


noncomputable def E71RS1 : RelationCertificate Table 2 ![![71, 0, 0], ![34, 1, 0]]
  ![-116, -7, 2] ![![2, 0, 0], ![-53, -4, 1]] where
    su := ![![142, 0, 0], ![68, 2, 0]]
    hsu := by decide
    w := ![![-232, -14, 4], ![-242, 46, -4]]
    hw := by decide
    g := ![![![-41983, 191117, -45024], ![708117, 0, -22074]], ![![-20411, 93110, -21936], ![344982, 0, -10754]]]
    h := ![![![-968, -63, -2], ![2018, 72, 0]], ![![-1049, -64, -2], ![2187, 70, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {2} * I71N1 =  Ideal.span {B.equivFun.symm ![-116, -7, 2]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E71RS1 


noncomputable def E71RS2 : RelationCertificate Table 2 ![![71, 0, 0], ![-34, 1, 0]]
  ![-344722, -88813, -11989] ![![2, 0, 0], ![-53, -3, 1]] where
    su := ![![142, 0, 0], ![-68, 2, 0]]
    hsu := by decide
    w := ![![-689444, -177626, -23978], ![-4242130, -1092928, -147536]]
    hw := by decide
    g := ![![![-13, 869, -127], ![175, 0, 0]], ![![82, -509, 72], ![-72, 0, 0]]]
    h := ![![![-5788578, 189941, -1409], ![-12077774, 44025, 0]], ![![-35617077, 1168509, -8658], ![-74314453, 270475, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N2 : Ideal.span {2} * I71N2 =  Ideal.span {B.equivFun.symm ![-344722, -88813, -11989]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E71RS2 


noncomputable def E73RS1 : RelationCertificate Table 2 ![![73, 0, 0], ![-2, 1, 0]]
  ![-4514, -1163, -157] ![![2, 0, 0], ![-53, -3, 1]] where
    su := ![![146, 0, 0], ![-4, 2, 0]]
    hsu := by decide
    w := ![![-9028, -2326, -314], ![-55550, -14312, -1932]]
    hw := by decide
    g := ![![![28, -16, -6], ![141, 0, 0]], ![![1, 0, 1], ![-18, 0, 0]]]
    h := ![![![-14030, 6975, -9], ![-509838, 250, 0]], ![![-86327, 42908, -46], ![-3137048, 1196, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {2} * I73N1 =  Ideal.span {B.equivFun.symm ![-4514, -1163, -157]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E73RS1 
