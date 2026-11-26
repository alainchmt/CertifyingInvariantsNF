import IdealArithmetic.Examples.NF5_1_281250000_1_K.PrimesBelow5_1_281250000_1_KF0
import IdealArithmetic.Examples.NF5_1_281250000_1_K.ClassGroupData5_1_281250000_1_K

set_option linter.all false

noncomputable section


noncomputable def E3RS0 : RelationCertificate Table 1 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0]]
  ![3, 0, -1, -1, 0] ![![1, 0, 0, 0, 0]] where
    su := ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0]]
    hsu := by decide
    w := ![![3, 0, -1, -1, 0]]
    hw := by decide
    g := ![![![6961, -1212, -623, 267, 352]], ![![3520, -613, -315, 135, 178]]]
    h := ![![![1, 0, 0, -2, 0], ![0, -1, 1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {1} * I3N0 =  Ideal.span {B.equivFun.symm ![3, 0, -1, -1, 0]} * ((1 : Ideal O)) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowUnit E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 1 ![![3, 0, 0, 0, 0], ![1, 0, 1, 0, 0]]
  ![-1319, -99181, 40582, 115171, 35448] ![![1, 0, 0, 0, 0]] where
    su := ![![3, 0, 0, 0, 0], ![1, 0, 1, 0, 0]]
    hsu := by decide
    w := ![![-1319, -99181, 40582, 115171, 35448]]
    hw := by decide
    g := ![![![-2913074465817, 507183754829, 260700684108, -111719743343, -147297416058]], ![![-3205419688799, 558082813413, 286863626567, -122931517591, -162079632046]]]
    h := ![![![-43560, -75202, -37951, -172318, -2114], ![129361, 126425, 4179, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {1} * I3N1 =  Ideal.span {B.equivFun.symm ![-1319, -99181, 40582, 115171, 35448]} * ((1 : Ideal O)) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowUnit E3RS1 


noncomputable def E7RS0 : RelationCertificate Table 1 ![![7, 0, 0, 0, 0], ![3, 6, 1, 0, 0]]
  ![-41, 23, 6, -5, -4] ![![1, 0, 0, 0, 0]] where
    su := ![![7, 0, 0, 0, 0], ![3, 6, 1, 0, 0]]
    hsu := by decide
    w := ![![-41, 23, 6, -5, -4]]
    hw := by decide
    g := ![![![13, -11, 0, 5, -2]], ![![-3, 5, 1, -5, 2]]]
    h := ![![![16, 23, -33, -15, 8], ![-51, 56, -6, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {1} * I7N0 =  Ideal.span {B.equivFun.symm ![-41, 23, 6, -5, -4]} * ((1 : Ideal O)) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowUnit E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 1 ![![7, 0, 0, 0, 0], ![5, 1, 1, 5, 0]]
  ![13, -11, 0, 5, -2] ![![1, 0, 0, 0, 0]] where
    su := ![![7, 0, 0, 0, 0], ![5, 1, 1, 5, 0]]
    hsu := by decide
    w := ![![13, -11, 0, 5, -2]]
    hw := by decide
    g := ![![![-41, 23, 6, -5, -4]], ![![-175, 72, 31, 0, -10]]]
    h := ![![![-56, -11, -9, -55, 4], ![81, -3, 0, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {1} * I7N1 =  Ideal.span {B.equivFun.symm ![13, -11, 0, 5, -2]} * ((1 : Ideal O)) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowUnit E7RS1 


noncomputable def E13RS0 : RelationCertificate Table 1 ![![13, 0, 0, 0, 0], ![11, 4, 1, 0, 0]]
  ![680950399, -118557553, -60940507, 26115228, 34431744] ![![1, 0, 0, 0, 0]] where
    su := ![![13, 0, 0, 0, 0], ![11, 4, 1, 0, 0]]
    hsu := by decide
    w := ![![680950399, -118557553, -60940507, 26115228, 34431744]]
    hw := by decide
    g := ![![![127, -125, 3, 46, -38]], ![![-31, -39, 33, -33, -60]]]
    h := ![![![-8566801811, -2439338317, -1116648689, -408489764, -362607472], ![10186306722, -832035120, 474832888, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {1} * I13N0 =  Ideal.span {B.equivFun.symm ![680950399, -118557553, -60940507, 26115228, 34431744]} * ((1 : Ideal O)) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowUnit E13RS0 


noncomputable def E17RS0 : RelationCertificate Table 1 ![![17, 0, 0, 0, 0], ![9, 12, 1, 0, 0]]
  ![-3168037909, 551574432, 283518214, -121497906, -160189442] ![![1, 0, 0, 0, 0]] where
    su := ![![17, 0, 0, 0, 0], ![9, 12, 1, 0, 0]]
    hsu := by decide
    w := ![![-3168037909, 551574432, 283518214, -121497906, -160189442]]
    hw := by decide
    g := ![![![-50233373, 25406700, 5931938, -7246338, -4995154]], ![![-157949181, 78639312, 19156789, -21343776, -15261894]]]
    h := ![![![14312787814, 133893333840, 158502314471, 81490010982, 2968927704], ![-27387270083, -216331984428, -5063196041, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N0 : Ideal.span {1} * I17N0 =  Ideal.span {B.equivFun.symm ![-3168037909, 551574432, 283518214, -121497906, -160189442]} * ((1 : Ideal O)) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowUnit E17RS0 


noncomputable def E19RS0 : RelationCertificate Table 1 ![![19, 0, 0, 0, 0], ![8, 1, 0, 0, 0]]
  ![-79, 14, 7, -3, -4] ![![1, 0, 0, 0, 0]] where
    su := ![![19, 0, 0, 0, 0], ![8, 1, 0, 0, 0]]
    hsu := by decide
    w := ![![-79, 14, 7, -3, -4]]
    hw := by decide
    g := ![![![-61, 26, 9, -3, -4]], ![![-32, 13, 5, -1, -2]]]
    h := ![![![-541, 4065, 569, -1604, -444], ![1275, -9812, -651, 4216, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {1} * I19N0 =  Ideal.span {B.equivFun.symm ![-79, 14, 7, -3, -4]} * ((1 : Ideal O)) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowUnit E19RS0 


noncomputable def E19RS1 : RelationCertificate Table 1 ![![19, 0, 0, 0, 0], ![14, 1, 0, 0, 0]]
  ![-27191, 15375, 2554, -5797, -3282] ![![1, 0, 0, 0, 0]] where
    su := ![![19, 0, 0, 0, 0], ![14, 1, 0, 0, 0]]
    hsu := by decide
    w := ![![-27191, 15375, 2554, -5797, -3282]]
    hw := by decide
    g := ![![![21271, -4047, -1820, 913, 996]], ![![17246, -3173, -1506, 718, 830]]]
    h := ![![![-248957, 4009881, 454205, -661853, -105868], ![335928, -5464878, -297612, 1004105, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {1} * I19N1 =  Ideal.span {B.equivFun.symm ![-27191, 15375, 2554, -5797, -3282]} * ((1 : Ideal O)) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowUnit E19RS1 


noncomputable def E23RS0 : RelationCertificate Table 1 ![![23, 0, 0, 0, 0], ![12, 1, 0, 0, 0]]
  ![-62172582383, 10824619882, 5564030357, -2384389767, -3143709796] ![![1, 0, 0, 0, 0]] where
    su := ![![23, 0, 0, 0, 0], ![12, 1, 0, 0, 0]]
    hsu := by decide
    w := ![![-62172582383, 10824619882, 5564030357, -2384389767, -3143709796]]
    hw := by decide
    g := ![![![4919, -1866, -849, 209, 452]], ![![3156, -1251, -515, 121, 254]]]
    h := ![![![-123213530041, -240708012134, 103280929683, -5789776199788, -1008590958716], ![230978217380, 443010890132, -1200844367735, 11597224170336, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N0 : Ideal.span {1} * I23N0 =  Ideal.span {B.equivFun.symm ![-62172582383, 10824619882, 5564030357, -2384389767, -3143709796]} * ((1 : Ideal O)) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowUnit E23RS0 
