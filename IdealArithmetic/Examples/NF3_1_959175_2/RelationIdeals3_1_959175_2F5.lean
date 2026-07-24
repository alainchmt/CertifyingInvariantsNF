import IdealArithmetic.Examples.NF3_1_959175_2.PrimesBelow3_1_959175_2F5
import IdealArithmetic.Examples.NF3_1_959175_2.ClassGroupData3_1_959175_2

set_option linter.all false

noncomputable section


noncomputable def E263RS0 : RelationCertificate Table 4693 ![![263, 0, 0], ![33, 1, 0]]
  ![-698, 89, -117] ![![4693, 0, 0], ![2214, 1, 0]] where
    su := ![![1234259, 0, 0], ![154869, 4693, 0]]
    hsu := by decide
    w := ![![-3275714, 417677, -549081], ![-1567462, 197106, -258115]]
    hw := by decide
    g := ![![![39376120, -20390778367, -119836102], ![14234253, 43261260679, -2510]], ![![4940167, -2559003924, -15039203], ![1789469, 5429205978, -315]]]
    h := ![![![131430635, -825308964, -346076016], ![13353404, 7001384007, 0]], ![![62877270, -394833162, -165565011], ![6388342, 3349507526, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R263N0 : Ideal.span {4693} * I263N0 =  Ideal.span {B.equivFun.symm ![-698, 89, -117]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E263RS0 


noncomputable def E263RS1 : RelationCertificate Table 61009 ![![263, 0, 0], ![101, 1, 0]]
  ![-4348, 783, 78] ![![61009, 0, 0], ![16293, 1, 0]] where
    su := ![![16045367, 0, 0], ![6161909, 61009, 0]]
    hsu := by decide
    w := ![![-265267132, 47770047, 4758702], ![-70831449, 12750881, 1281189]]
    hw := by decide
    g := ![![![-14567871110, 50135220884811, 40007236185], ![-3068712208, -187753955428933, -3181]], ![![-5642141257, 19417350566576, 15494786230], ![-1188470815, -72717030233121, -1232]]]
    h := ![![![-148874448362, 3287561614467, 431677705680], ![-44672082312, -8733172045674, 0]], ![![-39752333114, 877842004392, 115266226719], ![-11928302539, -2331924432852, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R263N1 : Ideal.span {61009} * I263N1 =  Ideal.span {B.equivFun.symm ![-4348, 783, 78]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E263RS1 


noncomputable def E263RS2 : RelationCertificate Table 361 ![![263, 0, 0], ![129, 1, 0]]
  ![-7882, -319, -473] ![![361, 0, 0], ![48, 1, 0]] where
    su := ![![94943, 0, 0], ![46569, 361, 0]]
    hsu := by decide
    w := ![![-2845402, -115159, -170753], ![-464246, -18772, -27797]]
    hw := by decide
    g := ![![![21738473992, -202848824293, -57325018762], ![2328526333, 1591871674855, 0]], ![![10681783878, -99675225924, -28168189863], ![1144184245, 782208964658, 0]]]
    h := ![![![-2519196527, 75795136038, 7758188471], ![-947456779, -156954120642, 0]], ![![-411023605, 12366475753, 1265799557], ![-154583619, -25608098736, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R263N2 : Ideal.span {361} * I263N2 =  Ideal.span {B.equivFun.symm ![-7882, -319, -473]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E263RS2 


noncomputable def E271RS1 : RelationCertificate Table 19 ![![271, 0, 0], ![-107, 1, 0]]
  ![-91, -1, 9] ![![19, 0, 0], ![-9, 1, 0]] where
    su := ![![5149, 0, 0], ![-2033, 19, 0]]
    hsu := by decide
    w := ![![-1729, -19, 171], ![2489, -152, -76]]
    hw := by decide
    g := ![![![89368246, 229717246, -269602948], ![-30241933, 394035072, 0]], ![![-34944130, -89822410, 105418233], ![11825008, -154072800, 0]]]
    h := ![![![-1787722, -43664048, 5207399], ![544847, -108554240, 0]], ![![2574460, 62876475, -7498684], ![-784253, 156318720, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R271N1 : Ideal.span {19} * I271N1 =  Ideal.span {B.equivFun.symm ![-91, -1, 9]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E271RS1 
