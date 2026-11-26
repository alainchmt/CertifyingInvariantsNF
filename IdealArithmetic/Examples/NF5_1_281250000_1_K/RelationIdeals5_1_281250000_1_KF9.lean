import IdealArithmetic.Examples.NF5_1_281250000_1_K.PrimesBelow5_1_281250000_1_KF9
import IdealArithmetic.Examples.NF5_1_281250000_1_K.ClassGroupData5_1_281250000_1_K

set_option linter.all false

noncomputable section


noncomputable def E431RS0 : RelationCertificate Table 1 ![![431, 0, 0, 0, 0], ![139, 1, 0, 0, 0]]
  ![19966489, -10964426, -2007208, 3880678, 2293998] ![![1, 0, 0, 0, 0]] where
    su := ![![431, 0, 0, 0, 0], ![139, 1, 0, 0, 0]]
    hsu := by decide
    w := ![![19966489, -10964426, -2007208, 3880678, 2293998]]
    hw := by decide
    g := ![![![-56271635881, 9797229218, 5035934856, -2158080838, -2845333214]], ![![-18345980009, 3194145141, 1641842444, -703589082, -927650762]]]
    h := ![![![3053692815, -974905140460, -7383252172, 105390630228, 1517000898], ![-9468500984, 3022975345862, 3497243738, -326912546520, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R431N0 : Ideal.span {1} * I431N0 =  Ideal.span {B.equivFun.symm ![19966489, -10964426, -2007208, 3880678, 2293998]} * ((1 : Ideal O)) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowUnit E431RS0 


noncomputable def E439RS0 : RelationCertificate Table 1 ![![439, 0, 0, 0, 0], ![53, 1, 0, 0, 0]]
  ![-38714711599, 6740463734, 3464707792, -1484753546, -1957580230] ![![1, 0, 0, 0, 0]] where
    su := ![![439, 0, 0, 0, 0], ![53, 1, 0, 0, 0]]
    hsu := by decide
    w := ![![-38714711599, 6740463734, 3464707792, -1484753546, -1957580230]]
    hw := by decide
    g := ![![![82870679, -42646718, -9489248, 12801194, 8501742]], ![![10585873, -5444075, -1213612, 1631058, 1084726]]]
    h := ![![![-529442648444, 16737696299949, 845252352576, 30443660451192, 1148974092614], ![4384652980289, -138721256381022, 374711894846, -252200792118888, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R439N0 : Ideal.span {1} * I439N0 =  Ideal.span {B.equivFun.symm ![-38714711599, 6740463734, 3464707792, -1484753546, -1957580230]} * ((1 : Ideal O)) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowUnit E439RS0 


noncomputable def E457RS0 : RelationCertificate Table 1 ![![457, 0, 0, 0, 0], ![53, 1, 0, 0, 0]]
  ![-1563410347, 272198841, 139914874, -59958565, -79052712] ![![1, 0, 0, 0, 0]] where
    su := ![![457, 0, 0, 0, 0], ![53, 1, 0, 0, 0]]
    hsu := by decide
    w := ![![-1563410347, 272198841, 139914874, -59958565, -79052712]]
    hw := by decide
    g := ![![![2610672449, -1483901483, -242093436, 565493095, 317860386]], ![![323635561, -183769400, -30086128, 69888995, 39338264]]]
    h := ![![![-24374584753, 862858199703, 14653646729, -106631408298, -4025336568], ![210143807958, -7444076771196, -3249995255, 919749879432, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R457N0 : Ideal.span {1} * I457N0 =  Ideal.span {B.equivFun.symm ![-1563410347, 272198841, 139914874, -59958565, -79052712]} * ((1 : Ideal O)) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowUnit E457RS0 


noncomputable def E463RS0 : RelationCertificate Table 1 ![![463, 0, 0, 0, 0], ![212, 1, 0, 0, 0]]
  ![583, -744, 113, 603, 218] ![![1, 0, 0, 0, 0]] where
    su := ![![463, 0, 0, 0, 0], ![212, 1, 0, 0, 0]]
    hsu := by decide
    w := ![![583, -744, 113, 603, 218]]
    hw := by decide
    g := ![![![2699161, -470040, -241501, 103479, 136478]], ![![1244744, -216763, -111371, 47721, 62938]]]
    h := ![![![96301, -30075975, -153978, -22687110, -214050], ![-210315, 65685783, -207295, 49552684, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R463N0 : Ideal.span {1} * I463N0 =  Ideal.span {B.equivFun.symm ![583, -744, 113, 603, 218]} * ((1 : Ideal O)) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowUnit E463RS0 
