import IdealArithmetic.Examples.NF3_1_119660_3.PrimesBelow3_1_119660_3F1
import IdealArithmetic.Examples.NF3_1_119660_3.ClassGroupData3_1_119660_3

set_option linter.all false

noncomputable section


noncomputable def E53RS1 : RelationCertificate Table 3 ![![53, 0, 0], ![18, 1, 0]]
  ![-43148881, -7505037, -2215079] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![159, 0, 0], ![54, 3, 0]]
    hsu := by decide
    w := ![![-129446643, -22515111, -6645237], ![-146195214, -25428249, -7505037]]
    hw := by decide
    g := ![![![12885, -1831, -522], ![-610, 0, 0]], ![![3726, -333, -216], ![-108, 1, 0]]]
    h := ![![![-43180019, -2732902, -54996], ![124744007, 699709, 0]], ![![-48766918, -3086489, -62111], ![140884162, 790204, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {3} * I53N1 =  Ideal.span {B.equivFun.symm ![-43148881, -7505037, -2215079]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E53RS1 


noncomputable def E73RS1 : RelationCertificate Table 3 ![![73, 0, 0], ![-33, 1, 0]]
  ![-41, -15, 8] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![219, 0, 0], ![-99, 3, 0]]
    hsu := by decide
    w := ![![-123, -45, 24], ![528, -105, -15]]
    hw := by decide
    g := ![![![2305, 360, -29183], ![123, 87904, 0]], ![![-935, -147, 13072], ![-47, -39360, 0]]]
    h := ![![![-812, 28, 0], ![-1795, 8, 0]], ![![3542, -110, 0], ![7830, -5, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {3} * I73N1 =  Ideal.span {B.equivFun.symm ![-41, -15, 8]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E73RS1 
