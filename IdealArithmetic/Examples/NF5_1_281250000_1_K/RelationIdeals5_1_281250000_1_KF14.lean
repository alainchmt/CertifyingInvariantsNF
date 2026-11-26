import IdealArithmetic.Examples.NF5_1_281250000_1_K.PrimesBelow5_1_281250000_1_KF14
import IdealArithmetic.Examples.NF5_1_281250000_1_K.ClassGroupData5_1_281250000_1_K

set_option linter.all false

noncomputable section


noncomputable def E709RS0 : RelationCertificate Table 1 ![![709, 0, 0, 0, 0], ![356, 1, 0, 0, 0]]
  ![-20800112329, 3621424442, 1861470957, -797708139, -1051742012] ![![1, 0, 0, 0, 0]] where
    su := ![![709, 0, 0, 0, 0], ![356, 1, 0, 0, 0]]
    hsu := by decide
    w := ![![-20800112329, 3621424442, 1861470957, -797708139, -1051742012]]
    hw := by decide
    g := ![![![279299, -166190, -22787, 68851, 36764]], ![![141796, -84349, -11579, 34929, 18654]]]
    h := ![![![-3954364429021, 570645689295548, 1973878081177, -66504372710436, -373665556438], ![7875347135010, -1136504678191725, -1110777903871, 132463913886265, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R709N0 : Ideal.span {1} * I709N0 =  Ideal.span {B.equivFun.symm ![-20800112329, 3621424442, 1861470957, -797708139, -1051742012]} * ((1 : Ideal O)) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowUnit E709RS0 


noncomputable def E733RS0 : RelationCertificate Table 1 ![![733, 0, 0, 0, 0], ![20, 1, 0, 0, 0]]
  ![25861555370653, -4502652064862, -2314436261874, 991820278666, 1307670066810] ![![1, 0, 0, 0, 0]] where
    su := ![![733, 0, 0, 0, 0], ![20, 1, 0, 0, 0]]
    hsu := by decide
    w := ![![25861555370653, -4502652064862, -2314436261874, 991820278666, 1307670066810]]
    hw := by decide
    g := ![![![-608159759, 313158042, 69562142, -94161142, -62458494]], ![![-19150000, 9845107, 2196780, -2946790, -1961108]]]
    h := ![![![154320827569821, -8487050712801315, -66506095460952, 7202731908506647, 720322979370730], ![-5654565252665407, 311332911754198222, 70572994337843, -263997718104339140, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R733N0 : Ideal.span {1} * I733N0 =  Ideal.span {B.equivFun.symm ![25861555370653, -4502652064862, -2314436261874, 991820278666, 1307670066810]} * ((1 : Ideal O)) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowUnit E733RS0 


noncomputable def E757RS0 : RelationCertificate Table 1 ![![757, 0, 0, 0, 0], ![12, 1, 0, 0, 0]]
  ![-42997, 24588, 3927, -9485, -5288] ![![1, 0, 0, 0, 0]] where
    su := ![![757, 0, 0, 0, 0], ![12, 1, 0, 0, 0]]
    hsu := by decide
    w := ![![-42997, 24588, 3927, -9485, -5288]]
    hw := by decide
    g := ![![![-16988571121, 2957812256, 1520363503, -651531175, -859014296]], ![![-303346476, 52814443, 27147481, -11633685, -15338486]]]
    h := ![![![-925489, 328176880, 26506497, -10270587, -1712336], ![58379348, -20707354410, -514702, 648116532, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R757N0 : Ideal.span {1} * I757N0 =  Ideal.span {B.equivFun.symm ![-42997, 24588, 3927, -9485, -5288]} * ((1 : Ideal O)) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowUnit E757RS0 
