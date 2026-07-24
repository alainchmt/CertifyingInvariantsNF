import IdealArithmetic.Examples.NF3_1_108471_1.PrimesBelow3_1_108471_1F1
import IdealArithmetic.Examples.NF3_1_108471_1.ClassGroupData3_1_108471_1

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 5 ![![37, 0, 0], ![18, 1, 0]]
  ![-137, 42, -17] ![![5, 0, 0], ![-10, -2, 1]] where
    su := ![![185, 0, 0], ![90, 5, 0]]
    hsu := by decide
    w := ![![-685, 210, -85], ![-3055, 935, -380]]
    hw := by decide
    g := ![![![27, -11, -1], ![-26, 0, 0]], ![![15, -7, 0], ![-18, 0, 0]]]
    h := ![![![-11891, -773, -36], ![24435, 263, 0]], ![![-53045, -3424, -153], ![109003, 1117, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {5} * I37N1 =  Ideal.span {B.equivFun.symm ![-137, 42, -17]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E37RS1 


noncomputable def E41RS1 : RelationCertificate Table 5 ![![41, 0, 0], ![19, 1, 0]]
  ![4, -2, 1] ![![5, 0, 0], ![-10, -2, 1]] where
    su := ![![205, 0, 0], ![95, 5, 0]]
    hsu := by decide
    w := ![![20, -10, 5], ![185, -45, 15]]
    hw := by decide
    g := ![![![1, -1, -1], ![1, 0, 0]], ![![5, 0, -1], ![2, 0, 0]]]
    h := ![![![-62, -17, -4], ![134, 33, 0]], ![![-526, -35, -2], ![1137, 17, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {5} * I41N1 =  Ideal.span {B.equivFun.symm ![4, -2, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E41RS1 


noncomputable def E43RS1 : RelationCertificate Table 5 ![![43, 0, 0], ![18, 1, 0]]
  ![25907, -4798, -5174] ![![5, 0, 0], ![-10, -2, 1]] where
    su := ![![215, 0, 0], ![90, 5, 0]]
    hsu := by decide
    w := ![![129535, -23990, -25870], ![-287270, 79040, 75015]]
    hw := by decide
    g := ![![![48828975, -76240800, 33217301], ![-60518167, 0, 0]], ![![9854106, -15386031, 6703529], ![-12213069, 0, 0]]]
    h := ![![![-272095, -14390, 152], ![651444, -2342, 0]], ![![609938, 32334, -274], ![-1460266, 5357, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {5} * I43N1 =  Ideal.span {B.equivFun.symm ![25907, -4798, -5174]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E43RS1 


noncomputable def E71RS1 : RelationCertificate Table 5 ![![71, 0, 0], ![-17, 1, 0]]
  ![11276518, -3454249, 1401632] ![![5, 0, 0], ![-10, -2, 1]] where
    su := ![![355, 0, 0], ![-85, 5, 0]]
    hsu := by decide
    w := ![![56382590, -17271245, 7008160], ![251425895, -77017360, 31251365]]
    hw := by decide
    g := ![![![6380, -5251, -538], ![-10761, 0, 0]], ![![-891, 857, 169], ![1474, 0, 0]]]
    h := ![![![898450740, -56372169, 936272], ![3751689766, -13014736, 0]], ![![4006445577, -251379447, 4175108], ![16729844164, -58036479, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {5} * I71N1 =  Ideal.span {B.equivFun.symm ![11276518, -3454249, 1401632]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E71RS1 


noncomputable def E79RS1 : RelationCertificate Table 5 ![![79, 0, 0], ![16, 1, 0]]
  ![-58919813, 18048453, -7323528] ![![5, 0, 0], ![-10, -2, 1]] where
    su := ![![395, 0, 0], ![80, 5, 0]]
    hsu := by decide
    w := ![![-294599065, 90242265, -36617640], ![-1313700445, 402415750, -163288400]]
    hw := by decide
    g := ![![![6560, -9094, -3373], ![-10156, 0, 0]], ![![2511, -2848, -812], ![-4031, 0, 0]]]
    h := ![![![-55715355, -3326174, -135217], ![271412077, 671723, 0]], ![![-248450439, -14832329, -602965], ![1210302787, 2995311, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {5} * I79N1 =  Ideal.span {B.equivFun.symm ![-58919813, 18048453, -7323528]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E79RS1 
