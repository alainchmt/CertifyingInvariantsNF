import IdealArithmetic.Examples.NF5_1_405000000_1.PrimesBelow5_1_405000000_1F4
import IdealArithmetic.Examples.NF5_1_405000000_1.ClassGroupData5_1_405000000_1

set_option linter.all false

noncomputable section


noncomputable def E179RS1 : RelationCertificate Table 2 ![![179, 0, 0, 0, 0], ![82, 1, 0, 0, 0]]
  ![-35513, -11782, -6998, -1730, -2023] ![![2, 0, 0, 0, 0], ![-27, 2, 0, 1, 1]] where
    su := ![![358, 0, 0, 0, 0], ![164, 2, 0, 0, 0]]
    hsu := by decide
    w := ![![-71026, -23564, -13996, -3460, -4046], ![-454254, -150344, -89480, -22078, -25880]]
    hw := by decide
    g := ![![![797, 886, 3610, -1360, 2489], ![-9045, 0, 0, 0, 0]], ![![406, 1049, 1540, -564, 982], ![-4090, 0, 0, 0, 0]]]
    h := ![![![4725076407317, 84257549740, 3344052363895, 81489971562, -3731197], ![-10314496060308, 30883242965, -7300198248624, 166970560, 0]], ![![30192945194527, 538400517490, 21368287214836, 520715864491, -23842116], ![-65908990122530, 197342006736, -46647814067160, 1066931456, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N1 : Ideal.span {2} * I179N1 =  Ideal.span {B.equivFun.symm ![-35513, -11782, -6998, -1730, -2023]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E179RS1 


noncomputable def E179RS2 : RelationCertificate Table 2 ![![179, 0, 0, 0, 0], ![-59, 1, 0, 0, 0]]
  ![-7, -3, 1, 0, 1] ![![2, 0, 0, 0, 0], ![-27, 2, 0, 1, 1]] where
    su := ![![358, 0, 0, 0, 0], ![-118, 2, 0, 0, 0]]
    hsu := by decide
    w := ![![-14, -6, 2, 0, 2], ![204, 8, 4, -4, -6]]
    hw := by decide
    g := ![![![10, 47, 5, -1, -3], ![-23, 0, 0, 0, 0]], ![![11, -15, -2, 0, 0], ![9, 0, 0, 0, 0]]]
    h := ![![![103236515, -6563219, 353319245, -12082544, 7115], ![313209088, 3560500, 1071995006, -318396, 0]], ![![-1212096598, 77058989, -4148315933, 141860966, -83537], ![-3677377816, -41802673, -12586277198, 3738280, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N2 : Ideal.span {2} * I179N2 =  Ideal.span {B.equivFun.symm ![-7, -3, 1, 0, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E179RS2 


noncomputable def E197RS1 : RelationCertificate Table 2 ![![197, 0, 0, 0, 0], ![8, 1, 0, 0, 0]]
  ![121, -8, 2, -4, -3] ![![2, 0, 0, 0, 0], ![-27, 2, 0, 1, 1]] where
    su := ![![394, 0, 0, 0, 0], ![16, 2, 0, 0, 0]]
    hsu := by decide
    w := ![![242, -16, 4, -8, -6], ![-1092, 340, -72, 60, -22]]
    hw := by decide
    g := ![![![-10, -244, -98, -51, -41], ![23, 0, 0, 0, 0]], ![![5, -13, -6, -3, -3], ![2, 0, 0, 0, 0]]]
    h := ![![![86709, 364689, 2852917, 700412, -6427], ![-2135194, 28953, -70256700, 316529, 0]], ![![-365850, -1538206, -12032904, -2954170, 27105], ![9008988, -121596, 296325456, -1334924, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R197N1 : Ideal.span {2} * I197N1 =  Ideal.span {B.equivFun.symm ![121, -8, 2, -4, -3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E197RS1 
