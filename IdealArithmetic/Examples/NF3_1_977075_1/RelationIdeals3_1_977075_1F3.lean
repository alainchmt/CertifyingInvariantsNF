import IdealArithmetic.Examples.NF3_1_977075_1.PrimesBelow3_1_977075_1F3
import IdealArithmetic.Examples.NF3_1_977075_1.ClassGroupData3_1_977075_1

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 256 ![![139, 0, 0], ![69, 1, 0]]
  ![8893, -1075, -201] ![![256, 0, 0], ![-28, 1, 0]] where
    su := ![![35584, 0, 0], ![17664, 256, 0]]
    hsu := by decide
    w := ![![2276608, -275200, -51456], ![-182272, 24320, 4352]]
    hw := by decide
    g := ![![![10756867, 25478119369, -909946553], ![98347511, 232946318388, 0]], ![![5388097, 12761975249, -455791702], ![49262181, 116682676061, 0]]]
    h := ![![![33657295, 937758, 6520], ![-67802248, -906481, 0]], ![![-2693920, -75137, -523], ![5426872, 72714, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {256} * I139N1 =  Ideal.span {B.equivFun.symm ![8893, -1075, -201]} * (J0 ^ 8) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8 E139RS1 


noncomputable def E151RS1 : RelationCertificate Table 64 ![![151, 0, 0], ![50, 1, 0]]
  ![1293, -419, 39] ![![64, 0, 0], ![-28, 1, 0]] where
    su := ![![9664, 0, 0], ![3200, 64, 0]]
    hsu := by decide
    w := ![![82752, -26816, 2496], ![-49152, 15872, -1472]]
    hw := by decide
    g := ![![![-239732057, -41781877730, 1492515699], ![-547959046, -95521004771, 0]], ![![-77793838, -13558357747, 484326289], ![-177814509, -30996882509, 0]]]
    h := ![![![1711493, 42364, 163], ![-5168683, -24574, 0]], ![![-1016668, -25224, -98], ![3070322, 14775, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N1 : Ideal.span {64} * I151N1 =  Ideal.span {B.equivFun.symm ![1293, -419, 39]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E151RS1 


noncomputable def E163RS1 : RelationCertificate Table 8 ![![163, 0, 0], ![-54, 1, 0]]
  ![-1831, 1, 19] ![![8, 0, 0], ![4, 1, 0]] where
    su := ![![1304, 0, 0], ![-432, 8, 0]]
    hsu := by decide
    w := ![![-14648, 8, 152], ![-13632, -440, 96]]
    hw := by decide
    g := ![![![-3617, 995, -294], ![-1679, 1295, 0]], ![![1414, -431, 105], ![663, -426, 0]]]
    h := ![![![-797791, 16238, -27], ![-2408113, 4420, 0]], ![![-742368, 15101, -25], ![-2240820, 4087, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N1 : Ideal.span {8} * I163N1 =  Ideal.span {B.equivFun.symm ![-1831, 1, 19]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E163RS1 


noncomputable def E191RS0 : RelationCertificate Table 128 ![![191, 0, 0], ![17, 1, 0]]
  ![-233303, 75001, -6917] ![![128, 0, 0], ![-28, 1, 0]] where
    su := ![![24448, 0, 0], ![2176, 128, 0]]
    hsu := by decide
    w := ![![-29862784, 9600128, -885376], ![8828928, -2838272, 261760]]
    hw := by decide
    g := ![![![2178701042321323, 1335854981949156790, -47711885453595291], ![9959776193470032, 6107121338060197761, 0]], ![![182508987908357, 111904082300393033, -3996807159947593], ![834326801866907, 511591316473291962, 0]]]
    h := ![![![-896498, -52709, -62], ![10058695, 4925, 0]], ![![265036, 15577, 18], ![-2973700, -1393, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R191N0 : Ideal.span {128} * I191N0 =  Ideal.span {B.equivFun.symm ![-233303, 75001, -6917]} * (J0 ^ 7) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7 E191RS0 


noncomputable def E191RS1 : RelationCertificate Table 32 ![![191, 0, 0], ![73, 1, 0]]
  ![237, 93, 7] ![![32, 0, 0], ![4, 1, 0]] where
    su := ![![6112, 0, 0], ![2336, 32, 0]]
    hsu := by decide
    w := ![![7584, 2976, 224], ![-1376, 1120, 128]]
    hw := by decide
    g := ![![![386131, -100428283, -25131227], ![-3090116, 804199137, 0]], ![![145562, -37857791, -9473553], ![-1164849, 303153654, 0]]]
    h := ![![![249383, 4363, 13], ![-652492, -2476, 0]], ![![-44943, -836, -3], ![117590, 577, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R191N1 : Ideal.span {32} * I191N1 =  Ideal.span {B.equivFun.symm ![237, 93, 7]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E191RS1 


noncomputable def E191RS2 : RelationCertificate Table 64 ![![191, 0, 0], ![-91, 1, 0]]
  ![122469, -39371, 3631] ![![64, 0, 0], ![-28, 1, 0]] where
    su := ![![12224, 0, 0], ![-5824, 64, 0]]
    hsu := by decide
    w := ![![7838016, -2519744, 232384], ![-4634624, 1489920, -137408]]
    hw := by decide
    g := ![![![-8083057, -1408764616, 50323329], ![-18475558, -3220693199, 0]], ![![3893429, 678567237, -24239509], ![8899257, 1551328636, 0]]]
    h := ![![![2074424, -25360, 45], ![4352665, -4964, 0]], ![![-1226516, 15121, -28], ![-2573540, 3201, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R191N2 : Ideal.span {64} * I191N2 =  Ideal.span {B.equivFun.symm ![122469, -39371, 3631]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E191RS2 
