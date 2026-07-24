import IdealArithmetic.Examples.NF3_1_730732_1.PrimesBelow3_1_730732_1F0
import IdealArithmetic.Examples.NF3_1_730732_1.ClassGroupData3_1_730732_1

set_option linter.all false

noncomputable section


noncomputable def E3RS0 : RelationCertificate Table 1 ![![3, 0, 0], ![24, -2, 1]]
  ![1, 0, 0] ![![3, 0, 0], ![24, -2, 1]] where
    su := ![![3, 0, 0], ![24, -2, 1]]
    hsu := by decide
    w := ![![3, 0, 0], ![24, -2, 1]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {1} * I3N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 3 ![![3, 0, 0], ![0, 1, 0]]
  ![176725, 86664, 17471] ![![3, 0, 0], ![24, -2, 1]] where
    su := ![![9, 0, 0], ![0, 3, 0]]
    hsu := by decide
    w := ![![530175, 259992, 52413], ![-2654901, -1375947, -327861]]
    hw := by decide
    g := ![![![6349944888, 12340091469, -5440949790], ![40759181707, 0, 0]], ![![-5592103033, -10867348254, 4791593024], ![-35894727631, 0, 0]]]
    h := ![![![53868, 51998, -4257], ![-69330, 15121, 0]], ![![-268715, -275190, 16119], ![366921, -78822, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {3} * I3N1 =  Ideal.span {B.equivFun.symm ![176725, 86664, 17471]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS1 


noncomputable def E5RS0 : RelationCertificate Table 3 ![![5, 0, 0], ![22, -1, 1]]
  ![-7689642, 343111, -188421] ![![3, 0, 0], ![24, -2, 1]] where
    su := ![![15, 0, 0], ![66, -3, 3]]
    hsu := by decide
    w := ![![-23068926, 1029333, -565263], ![-248174757, 11073531, -6081081]]
    hw := by decide
    g := ![![![19, 180, -38], ![53, 0, 0]], ![![-81, -452, 171], ![-151, 0, 0]]]
    h := ![![![-76684, 2202, 28736], ![-332101, 0, 0]], ![![-824963, 23689, 309141], ![-3572732, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {3} * I5N0 =  Ideal.span {B.equivFun.symm ![-7689642, 343111, -188421]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 3 ![![5, 0, 0], ![1, 1, 0]]
  ![-91608183094118, 4087547289537, -2244695586694] ![![3, 0, 0], ![24, -2, 1]] where
    su := ![![15, 0, 0], ![3, 3, 0]]
    hsu := by decide
    w := ![![-274824549282354, 12262641868611, -6734086760082], ![-2956553579252682, 131921103127098, -72445086749013]]
    hw := by decide
    g := ![![![96646, 613637, -363980], ![242876, 0, 0]], ![![357751, 3047743, -188378], ![767572, 0, 0]]]
    h := ![![![-12269438830082, 6869707246649, 11223477933470], ![-1079946316686, -29181042627022, 0]], ![![-131994224617945, 73904087540707, 120741811248355], ![-11618027415446, -313928709245723, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {3} * I5N1 =  Ideal.span {B.equivFun.symm ![-91608183094118, 4087547289537, -2244695586694]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 3 ![![7, 0, 0], ![23, -1, 1]]
  ![-3061, -930, 202] ![![3, 0, 0], ![24, -2, 1]] where
    su := ![![21, 0, 0], ![69, -3, 3]]
    hsu := by decide
    w := ![![-9183, -2790, 606], ![55458, 17484, -3099]]
    hw := by decide
    g := ![![![-134747, -261814, 115438], ![-864772, 0, 0]], ![![-551067, -1070899, 472177], ![-3537168, 0, 0]]]
    h := ![![![-66, -149, 45], ![-113, 0, 0]], ![![262, 936, -251], ![724, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {3} * I7N0 =  Ideal.span {B.equivFun.symm ![-3061, -930, 202]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 3 ![![7, 0, 0], ![1, 1, 0]]
  ![133, 56, 5] ![![3, 0, 0], ![24, -2, 1]] where
    su := ![![21, 0, 0], ![3, 3, 0]]
    hsu := by decide
    w := ![![399, 168, 15], ![-2151, -933, -105]]
    hw := by decide
    g := ![![![1744, 3429, -1512], ![11323, 0, 0]], ![![-425, -803, 354], ![-2654, 0, 0]]]
    h := ![![![12, 1, -19], ![-20, 69, 0]], ![![-28, 30, 93], ![-178, -343, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {3} * I7N1 =  Ideal.span {B.equivFun.symm ![133, 56, 5]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS1 


noncomputable def E13RS0 : RelationCertificate Table 3 ![![13, 0, 0], ![25, -4, 1]]
  ![16068155249744569, -716959361277522, 393721564572014] ![![3, 0, 0], ![24, -2, 1]] where
    su := ![![39, 0, 0], ![75, -12, 3]]
    hsu := by decide
    w := ![![48204465749233707, -2150878083832566, 1181164693716042], ![518582077616496006, -23139076599586860, 12706931429568939]]
    hw := by decide
    g := ![![![-1169995, -9756858, 929110], ![-2545580, 0, 0]], ![![1712839, 16170124, 1454533], ![3407612, 0, 0]]]
    h := ![![![275741051049063, 98492622499966, -8124561451712], ![499340863444270, 0, 0]], ![![2966413275505704, 1059580435381972, -87403768341077], ![5371892798290314, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {3} * I13N0 =  Ideal.span {B.equivFun.symm ![16068155249744569, -716959361277522, 393721564572014]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 3 ![![13, 0, 0], ![-6, 1, 0]]
  ![-113985, 5086, -2793] ![![3, 0, 0], ![24, -2, 1]] where
    su := ![![39, 0, 0], ![-18, 3, 0]]
    hsu := by decide
    w := ![![-341955, 15258, -8379], ![-3678741, 164145, -90141]]
    hw := by decide
    g := ![![![-10, -9, -19], ![4, 0, 0]], ![![-11, 68, -1], ![18, 0, 0]]]
    h := ![![![51089, -532467, 179059], ![-64523, -1165280, 0]], ![![549554, -5728253, 1926311], ![-694266, -12536045, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {3} * I13N1 =  Ideal.span {B.equivFun.symm ![-113985, 5086, -2793]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E13RS1 
