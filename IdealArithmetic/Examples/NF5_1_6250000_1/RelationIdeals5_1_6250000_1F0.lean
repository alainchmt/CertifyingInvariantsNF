import IdealArithmetic.Examples.NF5_1_6250000_1.PrimesBelow5_1_6250000_1F0
import IdealArithmetic.Examples.NF5_1_6250000_1.ClassGroupData5_1_6250000_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 2 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]]
  ![0, 1, -1, 0, -1] ![![2, 0, 0, 0, 0], ![2, 0, -2, -1, -3]] where
    su := ![![4, 0, 0, 0, 0], ![0, 2, 0, 0, 0]]
    hsu := by decide
    w := ![![0, 2, -2, 0, -2], ![0, 4, -2, 0, -2]]
    hw := by decide
    g := ![![![2, -3, 0, 0, 0], ![-1, 1, 0, 0, 1]], ![![-1, 0, 0, 0, 0], ![1, 0, 0, 0, 0]]]
    h := ![![![0, 0, 0, -3, -5], ![1, -1, 0, 0, -3]], ![![0, 0, 0, -3, -5], ![2, -1, 0, 0, -3]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {2} * I2N0 =  Ideal.span {B.equivFun.symm ![0, 1, -1, 0, -1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 1 ![![2, 0, 0, 0, 0], ![2, 0, -2, -1, -3]]
  ![1, 0, 0, 0, 0] ![![2, 0, 0, 0, 0], ![2, 0, -2, -1, -3]] where
    su := ![![2, 0, 0, 0, 0], ![2, 0, -2, -1, -3]]
    hsu := by decide
    w := ![![2, 0, 0, 0, 0], ![2, 0, -2, -1, -3]]
    hw := by decide
    g := ![![![18, 0, 7, 4, 12], ![-2, 8, 2, 0, 0]], ![![-11, 0, -1, -3, -6], ![3, -4, -2, 2, 0]]]
    h := ![![![18, 0, 7, 4, 12], ![-2, 8, 2, 0, 0]], ![![-11, 0, -1, -3, -6], ![3, -4, -2, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS1 


noncomputable def E2RS2 : RelationCertificate Table 2 ![![2, 0, 0, 0, 0], ![4, -2, -1, -1, -2]]
  ![4, -1, 5, 2, 7] ![![2, 0, 0, 0, 0], ![2, 0, -2, -1, -3]] where
    su := ![![4, 0, 0, 0, 0], ![8, -4, -2, -2, -4]]
    hsu := by decide
    w := ![![8, -2, 10, 4, 14], ![-4, -18, -8, -6, -10]]
    hw := by decide
    g := ![![![2513, -622, 851, 431, 1292], ![-488, 1329, 21, 0, 0]], ![![3358, -831, 1138, 576, 1728], ![-651, 1776, 28, 0, 0]]]
    h := ![![![2470, -3732, 3905, 902, 5953], ![320, 1866, 0, -192, 21]], ![![-1418, 2135, -2236, -518, -3410], ![-181, -1068, 0, 108, -15]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N2 : Ideal.span {2} * I2N2 =  Ideal.span {B.equivFun.symm ![4, -1, 5, 2, 7]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS2 


noncomputable def E3RS0 : RelationCertificate Table 4 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0]]
  ![45, 34, 44, 23, 57] ![![4, 0, 0, 0, 0], ![4, 2, -2, -1, -4]] where
    su := ![![12, 0, 0, 0, 0], ![0, 4, 0, 0, 0]]
    hsu := by decide
    w := ![![180, 136, 176, 92, 228], ![120, 96, 96, 52, 120]]
    hw := by decide
    g := ![![![-27628, 35992, -2623, 9817, -5175], ![-5599, -44445, -141, 0, 0]], ![![-27623, 35979, -2621, 9814, -5173], ![-5594, -44430, -141, 0, 0]]]
    h := ![![![15, -66, 0, -161, 19], ![-21, 44, 253, 0, 0]], ![![10, -36, 0, -91, 10], ![-11, 24, 143, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {4} * I3N0 =  Ideal.span {B.equivFun.symm ![45, 34, 44, 23, 57]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 4 ![![3, 0, 0, 0, 0], ![2, 3, -3, -1, -5]]
  ![15, 4, -6, -3, -11] ![![4, 0, 0, 0, 0], ![4, 2, -2, -1, -4]] where
    su := ![![12, 0, 0, 0, 0], ![8, 12, -12, -4, -20]]
    hsu := by decide
    w := ![![60, 16, -24, -12, -44], ![56, 52, -52, -20, -88]]
    hw := by decide
    g := ![![![-39963245, 51699868, -3912756, 13972640, -7825747], ![-7824337, -63716306, 470, 0, 0]], ![![-75949131, 98254293, -7436096, 26554647, -14872639], ![-14869959, -121091227, 893, 0, 0]]]
    h := ![![![1, 1, -1, 2, 2], ![-1, -2, 0, 0, -4]], ![![-2, 3, -3, 6, 5], ![-3, 0, 0, 0, -13]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {4} * I3N1 =  Ideal.span {B.equivFun.symm ![15, 4, -6, -3, -11]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E3RS1 


noncomputable def E3RS2 : RelationCertificate Table 2 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0]]
  ![1, 0, 2, 1, 3] ![![2, 0, 0, 0, 0], ![4, 2, -2, -1, -4]] where
    su := ![![6, 0, 0, 0, 0], ![2, 2, 0, 0, 0]]
    hsu := by decide
    w := ![![2, 0, 4, 2, 6], ![4, -2, 6, 2, 8]]
    hw := by decide
    g := ![![![-85, 142, -6, 43, -5], ![-19, -88, -6, 0, 0]], ![![-15, 18, -1, 5, -2], ![-1, -11, 0, 0, 0]]]
    h := ![![![0, 39, 40, 87, -9], ![1, 27, -145, 0, -15]], ![![0, 52, 54, 117, -12], ![2, 36, -195, 0, -20]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N2 : Ideal.span {2} * I3N2 =  Ideal.span {B.equivFun.symm ![1, 0, 2, 1, 3]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E3RS2 


noncomputable def E5RS0 : RelationCertificate Table 4 ![![5, 0, 0, 0, 0], ![2, 1, 0, 0, 0]]
  ![-4, 3, -1, 0, -1] ![![4, 0, 0, 0, 0], ![2, 11, -9, -3, -14]] where
    su := ![![20, 0, 0, 0, 0], ![8, 4, 0, 0, 0]]
    hsu := by decide
    w := ![![-16, 12, -4, 0, -4], ![-36, -48, 48, 16, 76]]
    hw := by decide
    g := ![![![324092, -41024, -36599, 14759, 13655], ![72767, 159975, -711, 0, 0]], ![![252102, -31913, -28468, 11481, 10624], ![56604, 124440, -553, 0, 0]]]
    h := ![![![-2200, -1291, -288, -276, -365], ![5270, 515, 310, 152, 0]], ![![545, 321, 92, 92, 95], ![-1310, -106, -133, -38, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {4} * I5N0 =  Ideal.span {B.equivFun.symm ![-4, 3, -1, 0, -1]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E5RS0 


noncomputable def E11RS0 : RelationCertificate Table 2 ![![11, 0, 0, 0, 0], ![-3, 9, -3, -1, -5]]
  ![-1, -9, 9, 3, 14] ![![2, 0, 0, 0, 0], ![4, 2, -2, -1, -4]] where
    su := ![![22, 0, 0, 0, 0], ![-6, 18, -6, -2, -10]]
    hsu := by decide
    w := ![![-2, -18, 18, 6, 28], ![12, -48, 36, 10, 56]]
    hw := by decide
    g := ![![![4433, -4705, 793, -883, 1886], ![41, 2709, -301, 0, 0]], ![![4388, -4648, 789, -866, 1879], ![36, 2673, -301, 0, 0]]]
    h := ![![![-1406, -854, 2206, 206, 535], ![-1164, -3944, 47, 0, 0]], ![![-2955, -1785, 4629, 428, 1117], ![-2455, -8280, 102, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {2} * I11N0 =  Ideal.span {B.equivFun.symm ![-1, -9, 9, 3, 14]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 2 ![![11, 0, 0, 0, 0], ![-1, 4, -2, -1, -3]]
  ![-1, 4, -2, -1, -3] ![![2, 0, 0, 0, 0], ![4, 2, -2, -1, -4]] where
    su := ![![22, 0, 0, 0, 0], ![-2, 8, -4, -2, -6]]
    hsu := by decide
    w := ![![-2, 8, -4, -2, -6], ![-16, 14, -6, 2, -8]]
    hw := by decide
    g := ![![![9, 6, 10, 5, 13], ![-1, 0, 0, 0, 0]], ![![20, -31, 4, -7, 8], ![4, 18, 0, 0, 0]]]
    h := ![![![-12, -8, 8, -4, -12], ![1, -44, 0, 0, 0]], ![![-15885, -10655, 10325, -4770, -15803], ![449, -57708, -684, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {2} * I11N1 =  Ideal.span {B.equivFun.symm ![-1, 4, -2, -1, -3]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E11RS1 


noncomputable def E11RS2 : RelationCertificate Table 2 ![![11, 0, 0, 0, 0], ![4, 1, 0, 0, 0]]
  ![0, -9, 7, 2, 11] ![![2, 0, 0, 0, 0], ![2, 0, -2, -1, -3]] where
    su := ![![22, 0, 0, 0, 0], ![8, 2, 0, 0, 0]]
    hsu := by decide
    w := ![![0, -18, 14, 4, 22], ![6, -30, 18, 4, 28]]
    hw := by decide
    g := ![![![6, 3, -4, -2, -7], ![-5, 0, 0, 0, -1]], ![![0, 4, -5, -3, -7], ![-4, -3, 0, 0, -3]]]
    h := ![![![-489, -128, -105, -141, -179], ![1221, 36, 199, 165, 0]], ![![-561, -148, -124, -164, -206], ![1401, 41, 238, 190, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N2 : Ideal.span {2} * I11N2 =  Ideal.span {B.equivFun.symm ![0, -9, 7, 2, 11]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E11RS2 


noncomputable def E19RS2 : RelationCertificate Table 4 ![![19, 0, 0, 0, 0], ![9, 1, 0, 0, 0]]
  ![-2, -3, -3, -2, -5] ![![4, 0, 0, 0, 0], ![2, 11, -9, -3, -14]] where
    su := ![![76, 0, 0, 0, 0], ![36, 4, 0, 0, 0]]
    hsu := by decide
    w := ![![-8, -12, -12, -8, -20], ![12, 16, -8, 0, -16]]
    hw := by decide
    g := ![![![-25687, 3077, 2890, -1135, -1198], ![-5767, -12720, -54, 0, 0]], ![![-12390, 1483, 1395, -547, -576], ![-2781, -6135, -26, 0, 0]]]
    h := ![![![18437023, 2471558, 6186479, 1376950, -4619], ![-38925042, 566406, -13124904, 7313, 0]], ![![-11104689, -1488639, -3726115, -829338, 2780], ![23444700, -341120, 7905123, -4402, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N2 : Ideal.span {4} * I19N2 =  Ideal.span {B.equivFun.symm ![-2, -3, -3, -2, -5]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E19RS2 


noncomputable def E23RS2 : RelationCertificate Table 2 ![![23, 0, 0, 0, 0], ![-4, 1, 0, 0, 0]]
  ![-8, -7, -3, -2, -3] ![![2, 0, 0, 0, 0], ![2, 0, -2, -1, -3]] where
    su := ![![46, 0, 0, 0, 0], ![-8, 2, 0, 0, 0]]
    hsu := by decide
    w := ![![-16, -14, -6, -4, -6], ![14, 6, 34, 16, 48]]
    hw := by decide
    g := ![![![-59074, 7967, -18965, -10279, -30840], ![11295, -28665, -3185, 0, 0]], ![![8444, -1140, 2712, 1470, 4410], ![-1614, 4098, 455, 0, 0]]]
    h := ![![![-6025, 6727, -22044, 11059, -537], ![-33870, -1709, -126665, 1029, 0]], ![![4835, -5371, 17593, -8826, 432], ![27180, 1390, 101090, -826, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N2 : Ideal.span {2} * I23N2 =  Ideal.span {B.equivFun.symm ![-8, -7, -3, -2, -3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E23RS2 
