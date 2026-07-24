import IdealArithmetic.Examples.NF3_1_884199_1.PrimesBelow3_1_884199_1F0
import IdealArithmetic.Examples.NF3_1_884199_1.ClassGroupData3_1_884199_1

set_option linter.all false

noncomputable section


noncomputable def E3RS0 : RelationCertificate Table 5 ![![3, 0, 0], ![-38, -1, 1]]
  ![-5547275, -310135, 133156] ![![5, 0, 0], ![-38, -3, 1]] where
    su := ![![15, 0, 0], ![-190, -5, 5]]
    hsu := by decide
    w := ![![-27736375, -1550675, 665780], ![-35757735, 2714390, -92940]]
    hw := by decide
    g := ![![![-849420536, -29451475753, -12357065945], ![21655068578, 0, 0]], ![![-7006683995, -242938766552, -101930727807], ![178627913006, 0, 0]]]
    h := ![![![-6831602, -37601549, -19974324], ![92409373, 10784415, 0]], ![![-9413455, -51444021, -27559733], ![127198527, 14845972, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {5} * I3N0 =  Ideal.span {B.equivFun.symm ![-5547275, -310135, 133156]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 25 ![![3, 0, 0], ![-1, 1, 0]]
  ![-16, 1, 0] ![![25, 0, 0], ![-28, -3, 1]] where
    su := ![![75, 0, 0], ![-25, 25, 0]]
    hsu := by decide
    w := ![![-400, 25, 0], ![775, 75, -25]]
    hw := by decide
    g := ![![![22, 2, -1], ![22, 0, 0]], ![![-1, -2, -1], ![10, 0, 0]]]
    h := ![![![-3332, -908, 11], ![811, 0, 33]], ![![5960, 1623, -20], ![-1444, 0, -59]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {25} * I3N1 =  Ideal.span {B.equivFun.symm ![-16, 1, 0]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E3RS1 


noncomputable def E5RS0 : RelationCertificate Table 25 ![![5, 0, 0], ![2, 1, 0]]
  ![10079, 2586, 489] ![![25, 0, 0], ![-28, -3, 1]] where
    su := ![![125, 0, 0], ![50, 25, 0]]
    hsu := by decide
    w := ![![251975, 64650, 12225], ![30400, 7800, 1475]]
    hw := by decide
    g := ![![![69, -9, 1], ![-40, 0, 0]], ![![13, 14, -3], ![6, 0, 0]]]
    h := ![![![-501, 32440, 33279], ![6292, -55302, 0]], ![![-62, 3913, 4015], ![763, -6672, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {25} * I5N0 =  Ideal.span {B.equivFun.symm ![10079, 2586, 489]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 125 ![![5, 0, 0], ![-2, 1, 0]]
  ![-6378, -257, 133] ![![125, 0, 0], ![-53, -28, 1]] where
    su := ![![625, 0, 0], ![-250, 125, 0]]
    hsu := by decide
    w := ![![-797250, -32125, 16625], ![-978250, -17000, 15875]]
    hw := by decide
    g := ![![![-7479, -1503, -466], ![3610, 0, 0]], ![![-20804, -4202, -1291], ![9858, 0, 0]]]
    h := ![![![-1274, -2552, 7526], ![4, -12499, 0]], ![![-1564, -3131, 9335], ![3, -15516, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {125} * I5N1 =  Ideal.span {B.equivFun.symm ![-6378, -257, 133]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E5RS1 


noncomputable def E5RS2 : RelationCertificate Table 125 ![![5, 0, 0], ![-1, 1, 0]]
  ![48, 2, -1] ![![125, 0, 0], ![-53, -28, 1]] where
    su := ![![625, 0, 0], ![-125, 125, 0]]
    hsu := by decide
    w := ![![6000, 250, -125], ![7375, 125, -125]]
    hw := by decide
    g := ![![![2, 1, 0], ![4, 0, 0]], ![![5, 2, 0], ![7, 0, 0]]]
    h := ![![![10, 0, 1], ![2, -2, 0]], ![![12, 0, 1], ![1, -2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N2 : Ideal.span {125} * I5N2 =  Ideal.span {B.equivFun.symm ![48, 2, -1]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E5RS2 


noncomputable def E7RS0 : RelationCertificate Table 125 ![![7, 0, 0], ![-37, -2, 1]]
  ![-25141616, -23999, 324665] ![![125, 0, 0], ![-53, -28, 1]] where
    su := ![![875, 0, 0], ![-4625, -250, 125]]
    hsu := by decide
    w := ![![-3142702000, -2999875, 40583125], ![-1683363250, 212649750, -21502375]]
    hw := by decide
    g := ![![![-40448332133, -8192953087, -2504288230], ![18965280046, 0, 0]], ![![-57097520675, -11565305253, -3535093822], ![26771696483, 0, 0]]]
    h := ![![![-134908, 183423, -47045], ![653980, 0, 0]], ![![-86281, 342356, -74238], ![347647, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {125} * I7N0 =  Ideal.span {B.equivFun.symm ![-25141616, -23999, 324665]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 5 ![![7, 0, 0], ![-1, 1, 0]]
  ![-19236584, -2457081, 740583] ![![5, 0, 0], ![-38, -3, 1]] where
    su := ![![35, 0, 0], ![-5, 5, 0]]
    hsu := by decide
    w := ![![-96182920, -12285405, 3702915], ![-879710765, -32198520, 17688805]]
    hw := by decide
    g := ![![![-50097838487, -1737013834854, -728805397785], ![1277190794109, 0, 0]], ![![-106386545437, -3688680126047, -1547673330297], ![2712211155060, 0, 0]]]
    h := ![![![-5402164, 2303069, 89379], ![-18578564, 38310, 0]], ![![-24659796, -1394755, -49528654], ![3323581, 116746113, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {5} * I7N1 =  Ideal.span {B.equivFun.symm ![-19236584, -2457081, 740583]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS1 


noncomputable def E11RS0 : RelationCertificate Table 125 ![![11, 0, 0], ![3, 1, 0]]
  ![-1711, -439, -83] ![![125, 0, 0], ![-53, -28, 1]] where
    su := ![![1375, 0, 0], ![375, 125, 0]]
    hsu := by decide
    w := ![![-213875, -54875, -10375], ![716125, 183750, 34750]]
    hw := by decide
    g := ![![![108, 24, -2], ![99, 0, 0]], ![![-9, 5, 0], ![21, 0, 0]]]
    h := ![![![-1679, -611, -55], ![5586, 174, 0]], ![![5617, 2040, 181], ![-18686, -571, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {125} * I11N0 =  Ideal.span {B.equivFun.symm ![-1711, -439, -83]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 125 ![![11, 0, 0], ![-3, 1, 0]]
  ![-398727, -102303, -19345] ![![125, 0, 0], ![-53, -28, 1]] where
    su := ![![1375, 0, 0], ![-375, 125, 0]]
    hsu := by decide
    w := ![![-49840875, -12787875, -2418125], ![166910875, 42825000, 8098000]]
    hw := by decide
    g := ![![![967, -20, -19], ![-252, 0, 0]], ![![-776, 55, 13], ![334, 0, 0]]]
    h := ![![![-31142337, 10363925, -8552], ![-114055660, 24909, 0]], ![![104291815, -34707488, 28627], ![381958226, -83371, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {125} * I11N1 =  Ideal.span {B.equivFun.symm ![-398727, -102303, -19345]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E11RS1 


noncomputable def E11RS2 : RelationCertificate Table 25 ![![11, 0, 0], ![-1, 1, 0]]
  ![-1008578, 23858, 8015] ![![25, 0, 0], ![-28, -3, 1]] where
    su := ![![275, 0, 0], ![-25, 25, 0]]
    hsu := by decide
    w := ![![-25214450, 596450, 200375], ![27305400, 3148925, -982850]]
    hw := by decide
    g := ![![![2098322530, 948518690, 332993359], ![-2450623733, 0, 0]], ![![2835602276, 1281796159, 449995992], ![-3311690245, 0, 0]]]
    h := ![![![-90925, 1405, -8015], ![8403, 32060, 0]], ![![98579, 12164, 39314], ![-7847, -157256, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N2 : Ideal.span {25} * I11N2 =  Ideal.span {B.equivFun.symm ![-1008578, 23858, 8015]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E11RS2 


noncomputable def E31RS0 : RelationCertificate Table 25 ![![31, 0, 0], ![7, 1, 0]]
  ![231, 144, -32] ![![25, 0, 0], ![-28, -3, 1]] where
    su := ![![775, 0, 0], ![175, 25, 0]]
    hsu := by decide
    w := ![![5775, 3600, -800], ![75500, 5275, -2025]]
    hw := by decide
    g := ![![![5317, 2395, 839], ![-6159, 0, 0]], ![![3917, 1766, 619], ![-4547, 0, 0]]]
    h := ![![![448, 65, -2], ![-1951, 10, 0]], ![![5832, 873, 15], ![-25396, -182, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N0 : Ideal.span {25} * I31N0 =  Ideal.span {B.equivFun.symm ![231, 144, -32]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E31RS0 


noncomputable def E31RS1 : RelationCertificate Table 25 ![![31, 0, 0], ![10, 1, 0]]
  ![-204529396, 4087416, 1776873] ![![25, 0, 0], ![-28, -3, 1]] where
    su := ![![775, 0, 0], ![250, 25, 0]]
    hsu := by decide
    w := ![![-5113234900, 102185400, 44421825], ![5126616550, 608451675, -188009950]]
    hw := by decide
    g := ![![![-79714379627244, -36033821292861, -12650275981066], ![93098152698424, 0, 0]], ![![-66510152711790, -30065026764118, -10554830775598], ![77676981017929, 0, 0]]]
    h := ![![![-21796070616, -2743732308, -154010919], ![67547365970, 1592038454, 0]], ![![21997703002, 2766193042, 154202627], ![-68172372840, -1595933945, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {25} * I31N1 =  Ideal.span {B.equivFun.symm ![-204529396, 4087416, 1776873]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E31RS1 
