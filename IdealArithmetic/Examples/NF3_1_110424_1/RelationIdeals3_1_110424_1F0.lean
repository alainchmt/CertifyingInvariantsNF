import IdealArithmetic.Examples.NF3_1_110424_1.PrimesBelow3_1_110424_1F0
import IdealArithmetic.Examples.NF3_1_110424_1.ClassGroupData3_1_110424_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 3 ![![2, 0, 0], ![6, 2, 1]]
  ![399912, 34264, 30901] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![6, 0, 0], ![18, 6, 3]]
    hsu := by decide
    w := ![![1199736, 102792, 92703], ![1460874, 125166, 112881]]
    hw := by decide
    g := ![![![-248, 27, 6], ![92, 0, 0]], ![![1040, -166, 128], ![-401, 0, 0]]]
    h := ![![![-1474259, 2171627, 1392508], ![-1554875, 0, 171320]], ![![-1795146, 2644311, 1695606], ![-1893315, 0, 208610]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {3} * I2N0 =  Ideal.span {B.equivFun.symm ![399912, 34264, 30901]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS0 


noncomputable def E3RS0 : RelationCertificate Table 3 ![![3, 0, 0], ![6, 1, 1]]
  ![758221, -134798, -75988] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![9, 0, 0], ![18, 3, 3]]
    hsu := by decide
    w := ![![2274663, -404394, -227964], ![-5435121, 1383303, -580824]]
    hw := by decide
    g := ![![![725441146976, 133554795321, 61136113972], ![-197295450549, 0, 0]], ![![2992938742323, 551004478872, 252228102617], ![-813978087817, 0, 0]]]
    h := ![![![8155811, 1946220, -14209558], ![12223846, 0, -6065768]], ![![-19477599, -4602322, 33829191], ![-29212901, 0, 14493656]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {3} * I3N0 =  Ideal.span {B.equivFun.symm ![758221, -134798, -75988]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS0 


noncomputable def E11RS0 : RelationCertificate Table 3 ![![11, 0, 0], ![0, 1, 0]]
  ![28611, -4592, -4202] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![33, 0, 0], ![0, 3, 0]]
    hsu := by decide
    w := ![![85833, -13776, -12606], ![-281511, 66039, -14946]]
    hw := by decide
    g := ![![![1369051296, 252044381, 115375970], ![-372335635, 0, 0]], ![![579107283, 106614512, 48803916], ![-157497587, 0, 0]]]
    h := ![![![-143055, -144877, -437350], ![-13161, 801108, 0]], ![![469185, 475784, 1432694], ![43261, -2627436, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {3} * I11N0 =  Ideal.span {B.equivFun.symm ![28611, -4592, -4202]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E11RS0 


noncomputable def E11RS2 : RelationCertificate Table 3 ![![11, 0, 0], ![-1, 1, 0]]
  ![8205, 703, 634] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![33, 0, 0], ![-3, 3, 0]]
    hsu := by decide
    w := ![![24615, 2109, 1902], ![29973, 2568, 2316]]
    hw := by decide
    g := ![![![-58, 2, 12], ![23, 0, 0]], ![![64, -9, 2], ![-21, 0, 0]]]
    h := ![![![59662, 29890, 177542], ![-2699, -325388, 0]], ![![72648, 36397, 216188], ![-3295, -396216, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N2 : Ideal.span {3} * I11N2 =  Ideal.span {B.equivFun.symm ![8205, 703, 634]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E11RS2 


noncomputable def E29RS1 : RelationCertificate Table 3 ![![29, 0, 0], ![7, 1, 0]]
  ![595, 51, 46] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![87, 0, 0], ![21, 3, 0]]
    hsu := by decide
    w := ![![1785, 153, 138], ![2175, 186, 168]]
    hw := by decide
    g := ![![![-32, 2, 4], ![13, 0, 0]], ![![0, -1, 2], ![1, 0, 0]]]
    h := ![![![11173, 55049, 36806], ![4622, -177888, 0]], ![![13621, 67078, 44848], ![5604, -216756, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {3} * I29N1 =  Ideal.span {B.equivFun.symm ![595, 51, 46]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E29RS1 


noncomputable def E31RS1 : RelationCertificate Table 3 ![![31, 0, 0], ![12, 1, 0]]
  ![110878835, 9499971, 8567552] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![93, 0, 0], ![36, 3, 0]]
    hsu := by decide
    w := ![![332636505, 28499913, 25702656], ![405039123, 34703286, 31297170]]
    hw := by decide
    g := ![![![7721, -1611, 2066], ![-3110, 0, 0]], ![![6297, -792, 154], ![-2363, 0, 0]]]
    h := ![![![-950283791, -8385885958, -3602631400], ![-638364219, 18615023492, 0]], ![![-1157125295, -10211182005, -4386790508], ![-777312405, 22666823023, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {3} * I31N1 =  Ideal.span {B.equivFun.symm ![110878835, 9499971, 8567552]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E31RS1 
