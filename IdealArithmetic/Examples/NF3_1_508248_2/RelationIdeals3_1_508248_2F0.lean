import IdealArithmetic.Examples.NF3_1_508248_2.PrimesBelow3_1_508248_2F0
import IdealArithmetic.Examples.NF3_1_508248_2.ClassGroupData3_1_508248_2

set_option linter.all false

noncomputable section


noncomputable def E3RS0 : RelationCertificate Table 5 ![![3, 0, 0], ![1, 1, 0]]
  ![26967, 3551, 2470] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![15, 0, 0], ![5, 5, 0]]
    hsu := by decide
    w := ![![134835, 17755, 12350], ![360725, 47500, 33040]]
    hw := by decide
    g := ![![![402, 2, -2], ![85, 0, -18]], ![![149, -22, 14], ![30, 0, -4]]]
    h := ![![![24384, -22448, -77230], ![647, 23416, 0]], ![![65235, -60055, -206614], ![1730, 62645, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {5} * I3N0 =  Ideal.span {B.equivFun.symm ![26967, 3551, 2470]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS0 


noncomputable def E5RS0 : RelationCertificate Table 1 ![![5, 0, 0], ![1, 1, 0]]
  ![1, 0, 0] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![5, 0, 0], ![1, 1, 0]]
    hsu := by decide
    w := ![![5, 0, 0], ![1, 1, 0]]
    hw := by decide
    g := ![![![133, -2, -1], ![30, 0, -5]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![133, -2, -1], ![30, 0, -5]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {1} * I5N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 25 ![![5, 0, 0], ![2, 1, 0]]
  ![95607202979839, 12589492842167, 8756981818720] ![![25, 0, 0], ![-9, 1, 0]] where
    su := ![![125, 0, 0], ![50, 25, 0]]
    hsu := by decide
    w := ![![2390180074495975, 314737321054175, 218924545468000], ![322819678480475, 42508680359550, 29568128415750]]
    hw := by decide
    g := ![![![-6974092393390238394, -26305321879249972802, 37495690662559984347], ![1458460386450486915, -93739226656399974000, -1869]], ![![-2324697464463560962, -8768440626416730135, 12498563554186741117], ![486153462150212764, -31246408885466658000, -623]]]
    h := ![![![16404055278609, 1159205909754, 1751396363744], ![6793463293397, 0, 0]], ![![2215545141271, 156563299590, 236545027326], ![917530716432, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {25} * I5N1 =  Ideal.span {B.equivFun.symm ![95607202979839, 12589492842167, 8756981818720]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E5RS1 


noncomputable def E11RS0 : RelationCertificate Table 25 ![![11, 0, 0], ![-4, -4, 1]]
  ![-1686790330226901, -222115427779078, -154498738519780] ![![25, 0, 0], ![-9, 1, 0]] where
    su := ![![275, 0, 0], ![-100, -100, 25]]
    hsu := by decide
    w := ![![-42169758255672525, -5552885694476950, -3862468462994500], ![-5695482088129375, -749977289852475, -521668154073200]]
    hw := by decide
    g := ![![![75808203722215833, 285938167648463664, -407577186547445751], ![-15853426634059130, 1018942966368843128, 39]], ![![-29157001438138616, -109976218326743118, 156760456365267726], ![6097471784660194, -391901140911093512, -15]]]
    h := ![![![-135679583046591, -2527319187698, -18461587972580], ![48578729178600, 0, 0]], ![![-18324995611345, -341341799429, -2493437192093], ![6561082950095, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {25} * I11N0 =  Ideal.span {B.equivFun.symm ![-1686790330226901, -222115427779078, -154498738519780]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 5 ![![11, 0, 0], ![-2, 1, 0]]
  ![13, -1, 0] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![55, 0, 0], ![-10, 5, 0]]
    hsu := by decide
    w := ![![65, -5, 0], ![15, 10, -10]]
    hw := by decide
    g := ![![![456, -4, -3], ![91, 0, -17]], ![![-76, 1, 1], ![-14, 0, 3]]]
    h := ![![![-625, -11, 3240], ![120, -3564, 0]], ![![-123, -2, 638], ![24, -702, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {5} * I11N1 =  Ideal.span {B.equivFun.symm ![13, -1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E11RS1 


noncomputable def E13RS0 : RelationCertificate Table 5 ![![13, 0, 0], ![2, 1, 0]]
  ![-152117, -65196, 73530] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![65, 0, 0], ![10, 5, 0]]
    hsu := by decide
    w := ![![-760585, -325980, 367650], ![10125415, -53585, -725490]]
    hw := by decide
    g := ![![![21439340058, 2008656149, 2049562749], ![4689599243, 0, -16473]], ![![23709072218, 2221348871, 2266586138], ![5186084220, 0, -3230]]]
    h := ![![![-780317, 1533029, 3850360], ![-2113, -4998115, 0]], ![![11064739, -21827685, -54573846], ![23228, 70931490, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {5} * I13N0 =  Ideal.span {B.equivFun.symm ![-152117, -65196, 73530]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 5 ![![13, 0, 0], ![-1, 1, 0]]
  ![99, -8, 0] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![65, 0, 0], ![-5, 5, 0]]
    hsu := by decide
    w := ![![495, -40, 0], ![115, 75, -80]]
    hw := by decide
    g := ![![![25537, -270, -220], ![5054, 0, -972]], ![![16968, -186, -152], ![3361, 0, -648]]]
    h := ![![![190, -91, -920], ![-21, 1196, 0]], ![![42, -19, -202], ![1, 261, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {5} * I13N1 =  Ideal.span {B.equivFun.symm ![99, -8, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E13RS1 
