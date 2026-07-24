import IdealArithmetic.Examples.NF3_1_851175_3.PrimesBelow3_1_851175_3F1
import IdealArithmetic.Examples.NF3_1_851175_3.ClassGroupData3_1_851175_3

set_option linter.all false

noncomputable section


noncomputable def E41RS1 : RelationCertificate Table 49 ![![41, 0, 0], ![9, 1, 0]]
  ![413, -147, 9] ![![49, 0, 0], ![1, 1, 0]] where
    su := ![![2009, 0, 0], ![441, 49, 0]]
    hsu := by decide
    w := ![![20237, -7203, 441], ![1568, -196, -441]]
    hw := by decide
    g := ![![![107983322, -215829773, -323812062], ![-2200933, 5288930799, 0]], ![![23264778, -46499908, -69764385], ![-474161, 1139485087, 0]]]
    h := ![![![657804, -6544244, -1963383], ![-15183, 26832904, 0]], ![![50603, -503441, -151041], ![-1163, 2064224, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {49} * I41N1 =  Ideal.span {B.equivFun.symm ![413, -147, 9]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E41RS1 


noncomputable def E53RS1 : RelationCertificate Table 49 ![![53, 0, 0], ![10, 1, 0]]
  ![1260, -343, -111] ![![49, 0, 0], ![1, 1, 0]] where
    su := ![![2597, 0, 0], ![490, 49, 0]]
    hsu := by decide
    w := ![![61740, -16807, -5439], ![-10829, 4459, -1029]]
    hw := by decide
    g := ![![![-12911, -1156, -1398], ![-253, 17066, 0]], ![![-3174, -243, -282], ![-48, 3197, 0]]]
    h := ![![![-762, 8503, 2319], ![64, -41006, 0]], ![![131, -1504, -411], ![9, 7254, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {49} * I53N1 =  Ideal.span {B.equivFun.symm ![1260, -343, -111]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E53RS1 


noncomputable def E59RS1 : RelationCertificate Table 49 ![![59, 0, 0], ![25, 1, 0]]
  ![56, 0, -25] ![![49, 0, 0], ![1, 1, 0]] where
    su := ![![2891, 0, 0], ![1225, 49, 0]]
    hsu := by decide
    w := ![![2744, 0, -1225], ![-2744, 931, 0]]
    hw := by decide
    g := ![![![11759356980, -23504039964, -35263397305], ![-239687369, 575968822490, 0]], ![![4982793214, -9959368652, -14942162037], ![-101562740, 244055313196, 0]]]
    h := ![![![-71357, 1844019, 212773], ![1023, -4184544, 0]], ![![72266, -1868083, -215550], ![-984, 4239150, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {49} * I59N1 =  Ideal.span {B.equivFun.symm ![56, 0, -25]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E59RS1 


noncomputable def E67RS1 : RelationCertificate Table 49 ![![67, 0, 0], ![30, 1, 0]]
  ![-7, 0, -3] ![![49, 0, 0], ![1, 1, 0]] where
    su := ![![3283, 0, 0], ![1470, 49, 0]]
    hsu := by decide
    w := ![![-343, 0, -147], ![-343, 98, 0]]
    hw := by decide
    g := ![![![-1325171036, 2648688356, 3973859388], ![27010559, -64906370006, 0]], ![![-593348599, 1185956740, 1779305337], ![12094080, -29061987172, 0]]]
    h := ![![![-145, 4061, 393], ![31, -8778, 0]], ![![-133, 4092, 396], ![2, -8844, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {49} * I67N1 =  Ideal.span {B.equivFun.symm ![-7, 0, -3]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E67RS1 


noncomputable def E67RS2 : RelationCertificate Table 7 ![![67, 0, 0], ![-30, 1, 0]]
  ![0, 0, 1] ![![7, 0, 0], ![1, 1, 0]] where
    su := ![![469, 0, 0], ![-210, 7, 0]]
    hsu := by decide
    w := ![![0, 0, 7], ![112, -35, 0]]
    hw := by decide
    g := ![![![0, 7, 32], ![104, -73, 0]], ![![0, -4, -14], ![-39, 32, 0]]]
    h := ![![![21, 193, -20], ![32, 447, 0]], ![![28, -1, 0], ![62, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N2 : Ideal.span {7} * I67N2 =  Ideal.span {B.equivFun.symm ![0, 0, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E67RS2 


noncomputable def E71RS1 : RelationCertificate Table 7 ![![71, 0, 0], ![-15, 1, 0]]
  ![11193, 392, 298] ![![7, 0, 0], ![1, 1, 0]] where
    su := ![![497, 0, 0], ![-105, 7, 0]]
    hsu := by decide
    w := ![![78351, 2744, 2086], ![44177, 1547, 1176]]
    hw := by decide
    g := ![![![-66, 72, 91], ![6, -213, 0]], ![![13, -17, -20], ![4, 48, 0]]]
    h := ![![![-3831023, -53790506, 11526386], ![51814, -272791036, 0]], ![![-2160068, -30328947, 6498975], ![29192, -153809019, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {7} * I71N1 =  Ideal.span {B.equivFun.symm ![11193, 392, 298]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E71RS1 


noncomputable def E73RS1 : RelationCertificate Table 49 ![![73, 0, 0], ![-6, 1, 0]]
  ![29862, -10290, 205] ![![49, 0, 0], ![1, 1, 0]] where
    su := ![![3577, 0, 0], ![-294, 49, 0]]
    hsu := by decide
    w := ![![1463238, -504210, 10045], ![63112, 2107, -30870]]
    hw := by decide
    g := ![![![295864016, -581272434, -872215561], ![-5824655, 14248345458, 0]], ![![-24117354, 47782748, 71694286], ![482981, -1171096928, 0]]]
    h := ![![![-105516, -530388, 318139], ![1464, -7741314, 0]], ![![-4409, -22170, 13293], ![88, -323673, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {49} * I73N1 =  Ideal.span {B.equivFun.symm ![29862, -10290, 205]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E73RS1 


noncomputable def E79RS0 : RelationCertificate Table 7 ![![79, 0, 0], ![2, 1, 0]]
  ![-7, 0, 3] ![![7, 0, 0], ![1, 1, 0]] where
    su := ![![553, 0, 0], ![14, 7, 0]]
    hsu := by decide
    w := ![![-49, 0, 21], ![329, -112, 0]]
    hw := by decide
    g := ![![![299, -1077, -1632], ![-108, 3792, 0]], ![![-9, -14, -21], ![-2, 48, 0]]]
    h := ![![![1921, -5763, -5763], ![-3, 151760, 0]], ![![-13013, 39021, 39024], ![221, -1027632, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N0 : Ideal.span {7} * I79N0 =  Ideal.span {B.equivFun.symm ![-7, 0, 3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E79RS0 


noncomputable def E79RS1 : RelationCertificate Table 49 ![![79, 0, 0], ![33, 1, 0]]
  ![-1428, -49, -38] ![![49, 0, 0], ![1, 1, 0]] where
    su := ![![3871, 0, 0], ![1617, 49, 0]]
    hsu := by decide
    w := ![![-69972, -2401, -1862], ![-5635, -196, -147]]
    hw := by decide
    g := ![![![455761661623, -910954569092, -1366716230713], ![-9289651147, 22323031768314, 0]], ![![189419933506, -378603486065, -568023419570], ![-3860888782, 9277715852977, 0]]]
    h := ![![![838406, -28378582, -2504003], ![-8993, 65938733, 0]], ![![67498, -2285301, -201645], ![-681, 5309984, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {49} * I79N1 =  Ideal.span {B.equivFun.symm ![-1428, -49, -38]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E79RS1 
