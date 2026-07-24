import IdealArithmetic.Examples.NF3_1_132328_2.PrimesBelow3_1_132328_2F2
import IdealArithmetic.Examples.NF3_1_132328_2.ClassGroupData3_1_132328_2

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 4 ![![83, 0, 0], ![30, 1, 0]]
  ![-27331, 8799, 2594] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![332, 0, 0], ![120, 4, 0]]
    hsu := by decide
    w := ![![-109324, 35196, 10376], ![88008, -50220, 20192]]
    hw := by decide
    g := ![![![-1740777350463, 17404425239980, 12183073011594], ![3480717634765, -24366184541556, 51714]], ![![-669532213752, 6694009761221, 4685797169946], ![1338736333434, -9371609437733, 19890]]]
    h := ![![![569323, 17618, -64], ![-1576038, 3953, 0]], ![![-463506, -14445, 136], ![1283100, -3120, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {4} * I83N1 =  Ideal.span {B.equivFun.symm ![-27331, 8799, 2594]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E83RS1 


noncomputable def E97RS1 : RelationCertificate Table 4 ![![97, 0, 0], ![-17, 1, 0]]
  ![95319, -33491, -5390] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![388, 0, 0], ![-68, 4, 0]]
    hsu := by decide
    w := ![![381276, -133964, -21560], ![-105812, 97256, -72372]]
    hw := by decide
    g := ![![![64386022244437, -643828206656766, -450679510125890], ![-128764040541968, 901359388827579, -146475]], ![![-10901272404282, 109007948903294, 76305529241271], ![21801351023683, -152611113453183, 24800]]]
    h := ![![![1876647, -111699, 72], ![10702320, -6187, 0]], ![![-524103, 31356, -223], ![-2988914, 1769, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {4} * I97N1 =  Ideal.span {B.equivFun.symm ![95319, -33491, -5390]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E97RS1 
