import IdealArithmetic.Examples.NF3_1_161700_2.PrimesBelow3_1_161700_2F2
import IdealArithmetic.Examples.NF3_1_161700_2.ClassGroupData3_1_161700_2

set_option linter.all false

noncomputable section


noncomputable def E89RS1 : RelationCertificate Table 2 ![![89, 0, 0], ![17, 1, 0]]
  ![-7748712157, -949791793, -752414739] ![![2, 0, 0], ![1, 0, 1]] where
    su := ![![178, 0, 0], ![34, 2, 0]]
    hsu := by decide
    w := ![![-15497424314, -1899583586, -1504829478], ![-72051080404, -8831599814, -6996297418]]
    hw := by decide
    g := ![![![-1159266, 72537, 214595], ![-472333, 29110, 0]], ![![-253266, 12306, 50483], ![-101389, 6035, 0]]]
    h := ![![![-30485409292, -1869817374, -32123301], ![159144277343, 351093175, 0]], ![![-141733660438, -8693209859, -149348593], ![739898249340, 1632312678, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {2} * I89N1 =  Ideal.span {B.equivFun.symm ![-7748712157, -949791793, -752414739]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E89RS1 


noncomputable def E103RS1 : RelationCertificate Table 2 ![![103, 0, 0], ![-25, 1, 0]]
  ![-90247, 6149, 5263] ![![2, 0, 0], ![1, 0, 1]] where
    su := ![![206, 0, 0], ![-50, 2, 0]]
    hsu := by decide
    w := ![![-180494, 12298, 10526], ![320956, 62270, -95510]]
    hw := by decide
    g := ![![![-1527306389, -228719154, 160487814], ![-683409287, 70692, 0]], ![![258556230, 38693396, -27183917], ![115686159, -16851, 0]]]
    h := ![![![-1877674, 76628, -323], ![-7732407, 6422, 0]], ![![3331326, -135531, 197], ![13718644, -11341, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {2} * I103N1 =  Ideal.span {B.equivFun.symm ![-90247, 6149, 5263]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E103RS1 


noncomputable def E107RS1 : RelationCertificate Table 2 ![![107, 0, 0], ![28, 1, 0]]
  ![852032129521, 104437112593, 82733945895] ![![2, 0, 0], ![1, 0, 1]] where
    su := ![![214, 0, 0], ![56, 2, 0]]
    hsu := by decide
    w := ![![1704064259042, 208874225186, 165467891790], ![7922585615140, 971104184042, 769298183626]]
    hw := by decide
    g := ![![![5357388, -172569, -1395095], ![1981147, -47824, 0]], ![![1181060, 2548, -327566], ![426748, -13237, 0]]]
    h := ![![![35064613691131, 1346370739377, 20091445413], ![-133966486886482, -344508452216, 0]], ![![163023432101110, 6259586395196, 93409738261], ![-622840926500400, -1601698817019, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {2} * I107N1 =  Ideal.span {B.equivFun.symm ![852032129521, 104437112593, 82733945895]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E107RS1 


noncomputable def E109RS1 : RelationCertificate Table 2 ![![109, 0, 0], ![-17, 1, 0]]
  ![29569188, -1132430, -2529653] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![218, 0, 0], ![-34, 2, 0]]
    hsu := by decide
    w := ![![59138376, -2264860, -5059306], ![-197312934, 33496064, -6794580]]
    hw := by decide
    g := ![![![475931968928398, 46669564588862, 46213902507596], ![23334782294433, 0, 0]], ![![-41157422717342, -4035868828360, -3996464295529], ![-2017934414180, 0, 0]]]
    h := ![![![929514168, -55732826, 374701], ![5958086772, -7228677, 0]], ![![-3102266725, 186123638, -1357524], ![-19885200974, 24095471, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {2} * I109N1 =  Ideal.span {B.equivFun.symm ![29569188, -1132430, -2529653]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E109RS1 
