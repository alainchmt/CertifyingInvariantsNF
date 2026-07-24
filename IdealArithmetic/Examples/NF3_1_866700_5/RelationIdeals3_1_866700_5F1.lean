import IdealArithmetic.Examples.NF3_1_866700_5.PrimesBelow3_1_866700_5F1
import IdealArithmetic.Examples.NF3_1_866700_5.ClassGroupData3_1_866700_5

set_option linter.all false

noncomputable section


noncomputable def E37RS0 : RelationCertificate Table 8281 ![![37, 0, 0], ![18, 1, 0]]
  ![-1463, -168, -65] ![![8281, 0, 0], ![1119, 1, 0]] where
    su := ![![306397, 0, 0], ![149058, 8281, 0]]
    hsu := by decide
    w := ![![-12115103, -1391208, -538265], ![-1647919, -190463, -74529]]
    hw := by decide
    g := ![![![6139870283984451514070, -1168671167992369799804583, -13504643647095075130829], ![688545306096634639333, 8602458003199562858264100, 864]], ![![3069932892050562732581, -584335155739262583545912, -6752316874801231776658], ![344272400732437767277, 4301225849248384641694160, 432]]]
    h := ![![![-21173, 99516, 53794], ![-7596, -153111, 0]], ![![-2881, 13536, 7317], ![-1031, -20826, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N0 : Ideal.span {8281} * I37N0 =  Ideal.span {B.equivFun.symm ![-1463, -168, -65]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E37RS0 


noncomputable def E37RS1 : RelationCertificate Table 91 ![![37, 0, 0], ![-12, 1, 0]]
  ![609, -35, -13] ![![91, 0, 0], ![27, 1, 0]] where
    su := ![![3367, 0, 0], ![-1092, 91, 0]]
    hsu := by decide
    w := ![![55419, -3185, -1183], ![14287, -546, -728]]
    hw := by decide
    g := ![![![-101152789324, 594885968459, 234246959487], ![-23475157533, -1639731756725, 1882110]], ![![7057169447, -41503661139, -16342806764], ![1637801321, 114399859465, -131310]]]
    h := ![![![-927171, -1023127, 2200783], ![273056, -6263768, 0]], ![![-237515, -262101, 563788], ![69963, -1604628, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {91} * I37N1 =  Ideal.span {B.equivFun.symm ![609, -35, -13]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E37RS1 


noncomputable def E43RS1 : RelationCertificate Table 637 ![![43, 0, 0], ![12, 1, 0]]
  ![-3983, -497, -325] ![![637, 0, 0], ![-155, 1, 0]] where
    su := ![![27391, 0, 0], ![7644, 637, 0]]
    hsu := by decide
    w := ![![-2537171, -316589, -207025], ![561197, 70070, 45864]]
    hw := by decide
    g := ![![![-6834217507040705, -178077971622530385, 15536814754641637], ![1383399908899726, -761303922977469500, -2365]], ![![-1892774850908271, -49319692538411851, 4303007945022201], ![383140360050889, -210847389306095961, -655]]]
    h := ![![![-257245055, 817155117, 589281004], ![-52785686, -1949160269, 0]], ![![56899799, -180745801, -130342532], ![11675625, 431132996, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {637} * I43N1 =  Ideal.span {B.equivFun.symm ![-3983, -497, -325]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E43RS1 


noncomputable def E59RS1 : RelationCertificate Table 49 ![![59, 0, 0], ![1, 1, 0]]
  ![-63, -7, -3] ![![49, 0, 0], ![-8, 1, 0]] where
    su := ![![2891, 0, 0], ![49, 49, 0]]
    hsu := by decide
    w := ![![-3087, -343, -147], ![0, -49, -49]]
    hw := by decide
    g := ![![![33298621837, 11488809223, -73987192867], ![-5202044158, 278874803883, 0]], ![![564383715, 194725678, -1254020855], ![-88170238, 4726693992, 0]]]
    h := ![![![16412, -19148, -35561], ![-19, 161392, 0]], ![![-294, 341, 635], ![54, -2882, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {49} * I59N1 =  Ideal.span {B.equivFun.symm ![-63, -7, -3]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E59RS1 


noncomputable def E67RS1 : RelationCertificate Table 49 ![![67, 0, 0], ![2, 1, 0]]
  ![-6335, -791, -514] ![![49, 0, 0], ![-8, 1, 0]] where
    su := ![![3283, 0, 0], ![98, 49, 0]]
    hsu := by decide
    w := ![![-310415, -38759, -25186], ![-38122, -4753, -3087]]
    hw := by decide
    g := ![![![9674313, 3337859, -21495608], ![-1511322, 81021909, 0]], ![![264728, 91334, -588190], ![-41319, 2217023, 0]]]
    h := ![![![-115369, 153747, 249824], ![-1088, -1287594, 0]], ![![-14170, 18881, 30681], ![-84, -158130, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {49} * I67N1 =  Ideal.span {B.equivFun.symm ![-6335, -791, -514]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E67RS1 
