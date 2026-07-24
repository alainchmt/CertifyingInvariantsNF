import IdealArithmetic.Examples.NF3_1_567567_2.PrimesBelow3_1_567567_2F4
import IdealArithmetic.Examples.NF3_1_567567_2.ClassGroupData3_1_567567_2

set_option linter.all false

noncomputable section


noncomputable def E199RS0 : RelationCertificate Table 10 ![![199, 0, 0], ![82, 1, 0]]
  ![30516287, 1145713, 1025461] ![![10, 0, 0], ![22, 1, 1]] where
    su := ![![1990, 0, 0], ![820, 10, 0]]
    hsu := by decide
    w := ![![305162870, 11457130, 10254610], ![827308810, 31060740, 27800660]]
    hw := by decide
    g := ![![![78277790730613349, -34268839046105763, -3769646647076290], ![168407291038031179, -43570274855755398, 0]], ![![32156831116712757, -14077776844313375, -1548585996976898], ![69182392172639064, -17898844067623111, 0]]]
    h := ![![![264361239, 14032371050, 676307179], ![179447333, -33646025790, 0]], ![![716694059, 38042322106, 1833495954], ![486488665, -91215728695, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R199N0 : Ideal.span {10} * I199N0 =  Ideal.span {B.equivFun.symm ![30516287, 1145713, 1025461]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E199RS0 


noncomputable def E199RS1 : RelationCertificate Table 10 ![![199, 0, 0], ![-56, 1, 0]]
  ![-2493, 633, 181] ![![10, 0, 0], ![22, 1, 1]] where
    su := ![![1990, 0, 0], ![-560, 10, 0]]
    hsu := by decide
    w := ![![-24930, 6330, 1810], ![17050, -4120, -1680]]
    hw := by decide
    g := ![![![-55698167, 24444209, 2685652], ![-119822923, 31079114, 0]], ![![15584817, -6838747, -751416], ![33527606, -8694989, 0]]]
    h := ![![![-7344747, 226778781, -16494173], ![3206574, 820585152, 0]], ![![5022855, -155086025, 11279784], ![-2192717, -561169296, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R199N1 : Ideal.span {10} * I199N1 =  Ideal.span {B.equivFun.symm ![-2493, 633, 181]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E199RS1 


noncomputable def E199RS2 : RelationCertificate Table 10 ![![199, 0, 0], ![-26, 1, 0]]
  ![-1099, -41, -37] ![![10, 0, 0], ![22, 1, 1]] where
    su := ![![1990, 0, 0], ![-260, 10, 0]]
    hsu := by decide
    w := ![![-10990, -410, -370], ![-29770, -1120, -1000]]
    hw := by decide
    g := ![![![-2991, 1302, 143], ![-6415, 1662, 0]], ![![348, -158, -18], ![782, -201, 0]]]
    h := ![![![-36013, 461557, -73855], ![7041, 3674277, 0]], ![![-97541, 1250275, -200060], ![19163, 9952960, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R199N2 : Ideal.span {10} * I199N2 =  Ideal.span {B.equivFun.symm ![-1099, -41, -37]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E199RS2 


noncomputable def E211RS1 : RelationCertificate Table 50 ![![211, 0, 0], ![-82, 1, 0]]
  ![47255291901, 1774167419, 1587953963] ![![50, 0, 0], ![12, 1, 1]] where
    su := ![![10550, 0, 0], ![-4100, 50, 0]]
    hsu := by decide
    w := ![![2362764595050, 88708370950, 79397698150], ![808557043600, 30356717850, 27170530750]]
    hw := by decide
    g := ![![![340952, -52558, 7027], ![80945, -166668, 0]], ![![-132732, 20597, -2792], ![-31462, 64549, 0]]]
    h := ![![![-653135801631, 32908991910880, -1625223370203], ![409792074358, 85730929766699, 0]], ![![-223508323248, 11261721655667, -556164505831], ![140234142979, 29337813535239, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R211N1 : Ideal.span {50} * I211N1 =  Ideal.span {B.equivFun.symm ![47255291901, 1774167419, 1587953963]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E211RS1 
