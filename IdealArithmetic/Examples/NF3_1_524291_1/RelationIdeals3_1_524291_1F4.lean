import IdealArithmetic.Examples.NF3_1_524291_1.PrimesBelow3_1_524291_1F4
import IdealArithmetic.Examples.NF3_1_524291_1.ClassGroupData3_1_524291_1

set_option linter.all false

noncomputable section


noncomputable def E197RS1 : RelationCertificate Table 448 ![![197, 0, 0], ![-70, 1, 0]]
  ![-982, -99, -52] ![![448, 0, 0], ![-113, 1, 0]] where
    su := ![![88256, 0, 0], ![-31360, 448, 0]]
    hsu := by decide
    w := ![![-439936, -44352, -23296], ![103488, 10304, 5376]]
    hw := by decide
    g := ![![![25195896, -1578143443, 55374087], ![-9877387, -6201913508, -568]], ![![-8871720, 555684511, -19497925], ![3478262, 2183773151, 200]]]
    h := ![![![-90086, 3850701, -216956], ![51774, 10685070, 0]], ![![21263, -905827, 51036], ![-11978, -2513520, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R197N1 : Ideal.span {448} * I197N1 =  Ideal.span {B.equivFun.symm ![-982, -99, -52]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E197RS1 


noncomputable def E199RS1 : RelationCertificate Table 112 ![![199, 0, 0], ![-77, 1, 0]]
  ![-162, -25, -12] ![![112, 0, 0], ![-1, 1, 0]] where
    su := ![![22288, 0, 0], ![-8624, 112, 0]]
    hsu := by decide
    w := ![![-18144, -2800, -1344], ![-1568, -112, -112]]
    hw := by decide
    g := ![![![-314065943040, 311901066568, -623917399954], ![5588991217, 17469254223414, 1731901179]], ![![121523083964, -120685417636, 241415436028], ![-2162575803, -6759464675517, -670133063]]]
    h := ![![![898729, -43598062, 2235944], ![-566613, -111238217, 0]], ![![77886, -3777859, 193749], ![-49074, -9639013, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R199N1 : Ideal.span {112} * I199N1 =  Ideal.span {B.equivFun.symm ![-162, -25, -12]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E199RS1 
