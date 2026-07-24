import IdealArithmetic.Examples.NF3_1_588735_1.PrimesBelow3_1_588735_1F4
import IdealArithmetic.Examples.NF3_1_588735_1.ClassGroupData3_1_588735_1

set_option linter.all false

noncomputable section


noncomputable def E211RS1 : RelationCertificate Table 3025 ![![211, 0, 0], ![10, 1, 0]]
  ![-438, -137, -5] ![![3025, 0, 0], ![-1348, 1, 0]] where
    su := ![![638275, 0, 0], ![30250, 3025, 0]]
    hsu := by decide
    w := ![![-1324950, -414425, -15125], ![589875, 184525, 6050]]
    hw := by decide
    g := ![![![-448112528871, 402223747967206, -1490307830098], ![332654360755, 901947468937611, 1155277388]], ![![-27233357041, 24444537169991, -90571194097], ![20216565758, 54814487064108, 70210228]]]
    h := ![![![-500947352, -2261448874, -1256451215], ![-34459171, 53022241272, 0]], ![![223024457, 1006809243, 559378862], ![15341572, -23605787976, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R211N1 : Ideal.span {3025} * I211N1 =  Ideal.span {B.equivFun.symm ![-438, -137, -5]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E211RS1 
