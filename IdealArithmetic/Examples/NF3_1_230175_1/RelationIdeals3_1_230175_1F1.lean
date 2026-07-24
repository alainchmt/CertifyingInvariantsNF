import IdealArithmetic.Examples.NF3_1_230175_1.PrimesBelow3_1_230175_1F1
import IdealArithmetic.Examples.NF3_1_230175_1.ClassGroupData3_1_230175_1

set_option linter.all false

noncomputable section


noncomputable def E41RS0 : RelationCertificate Table 121 ![![41, 0, 0], ![1, 1, 0]]
  ![-4901, -1142, -516] ![![121, 0, 0], ![56, 1, 0]] where
    su := ![![4961, 0, 0], ![121, 121, 0]]
    hsu := by decide
    w := ![![-593021, -138182, -62436], ![-328636, -76593, -34606]]
    hw := by decide
    g := ![![![3691115, -1171736597, -104625224], ![-7975461, 2531930424, 0]], ![![139971, -44447098, -3968714], ![-302437, 96042880, 0]]]
    h := ![![![-120, -120, -471], ![19, 3759, 0]], ![![-67, -67, -261], ![31, 2083, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N0 : Ideal.span {121} * I41N0 =  Ideal.span {B.equivFun.symm ![-4901, -1142, -516]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E41RS0 


noncomputable def E41RS1 : RelationCertificate Table 11 ![![41, 0, 0], ![12, 1, 0]]
  ![-544, -46, 43] ![![11, 0, 0], ![1, 1, 0]] where
    su := ![![451, 0, 0], ![132, 11, 0]]
    hsu := by decide
    w := ![![-5984, -506, 473], ![3971, 55, -187]]
    hw := by decide
    g := ![![![1950, -178716, -901403], ![-16069, 1983200, 0]], ![![715, -54034, -272661], ![-4838, 599918, 0]]]
    h := ![![![-47408, -4402, -187], ![161932, 1542, 0]], ![![31385, 2911, 123], ![-107202, -1012, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {11} * I41N1 =  Ideal.span {B.equivFun.symm ![-544, -46, 43]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E41RS1 


noncomputable def E59RS1 : RelationCertificate Table 121 ![![59, 0, 0], ![19, 1, 0]]
  ![-104, -13, -1] ![![121, 0, 0], ![56, 1, 0]] where
    su := ![![7139, 0, 0], ![2299, 121, 0]]
    hsu := by decide
    w := ![![-12584, -1573, -121], ![-5929, -847, -121]]
    hw := by decide
    g := ![![![2864879, -909451124, -81205561], ![-6190185, 1965174575, 0]], ![![1061541, -336996615, -30090676], ![-2293687, 728194359, 0]]]
    h := ![![![-698, -52, -4], ![2162, 47, 0]], ![![-357, -34, -4], ![1106, 47, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {121} * I59N1 =  Ideal.span {B.equivFun.symm ![-104, -13, -1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E59RS1 
