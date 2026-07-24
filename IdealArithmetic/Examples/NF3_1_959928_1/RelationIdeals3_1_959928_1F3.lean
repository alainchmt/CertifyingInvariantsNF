import IdealArithmetic.Examples.NF3_1_959928_1.PrimesBelow3_1_959928_1F3
import IdealArithmetic.Examples.NF3_1_959928_1.ClassGroupData3_1_959928_1

set_option linter.all false

noncomputable section


noncomputable def E149RS1 : RelationCertificate Table 2 ![![149, 0, 0], ![74, 1, 0]]
  ![4324250697959, 1305667610078, 214249191481] ![![2, 0, 0], ![-31, -1, 1]] where
    su := ![![298, 0, 0], ![148, 2, 0]]
    hsu := by decide
    w := ![![8648501395918, 2611335220156, 428498382962], ![108084508785970, 32635120424364, 5355151732980]]
    hw := by decide
    g := ![![![335326, -579050, 914372], ![-4450701, 0, 0]], ![![152097, -164264, 406861], ![-2071706, 0, 0]]]
    h := ![![![-1684151190033, 638602241067746, 17031214692289], ![3449497000174, -1268718369979790, 0]], ![![-21047652738589, 7980921361474847, 212847335020758], ![43110033951929, -15855787671113226, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N1 : Ideal.span {2} * I149N1 =  Ideal.span {B.equivFun.symm ![4324250697959, 1305667610078, 214249191481]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E149RS1 


noncomputable def E151RS1 : RelationCertificate Table 50 ![![151, 0, 0], ![-16, 1, 0]]
  ![397651, 120067, 19702] ![![50, 0, 0], ![8, 1, 0]] where
    su := ![![7550, 0, 0], ![-800, 50, 0]]
    hsu := by decide
    w := ![![19882550, 6003350, 985100], ![8027900, 2423950, 397750]]
    hw := by decide
    g := ![![![-355413, 114141221, 25374598], ![2225968, -634365223, 0]], ![![37310, -11988053, -2665050], ![-233790, 66626279, 0]]]
    h := ![![![342498629, -21597756, 25804], ![3232305958, -1938351, 0]], ![![138289346, -8720444, 10419], ![1305095668, -782657, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N1 : Ideal.span {50} * I151N1 =  Ideal.span {B.equivFun.symm ![397651, 120067, 19702]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E151RS1 


noncomputable def E163RS1 : RelationCertificate Table 500 ![![163, 0, 0], ![36, 1, 0]]
  ![-46489, 65087, -10953] ![![500, 0, 0], ![-142, 1, 0]] where
    su := ![![81500, 0, 0], ![18000, 500, 0]]
    hsu := by decide
    w := ![![-23244500, 32543500, -5476500], ![3907000, -9749500, 1685500]]
    hw := by decide
    g := ![![![-436306, -731452, -14989], ![122643, -2088480, 0]], ![![-128902, -172762, -5048], ![36556, -463239, 0]]]
    h := ![![![173381297, 4815448, -127], ![-785033275, 4874, 0]], ![![-29551462, -820841, 29], ![133802670, -678, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N1 : Ideal.span {500} * I163N1 =  Ideal.span {B.equivFun.symm ![-46489, 65087, -10953]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E163RS1 


noncomputable def E167RS1 : RelationCertificate Table 10 ![![167, 0, 0], ![-69, 1, 0]]
  ![-77, 1, 1] ![![10, 0, 0], ![-27, -2, 1]] where
    su := ![![1670, 0, 0], ![-690, 10, 0]]
    hsu := by decide
    w := ![![-770, 10, 10], ![1710, 200, -60]]
    hw := by decide
    g := ![![![-40250863, -4038776, -5456753], ![108939477, 13592986, 0]], ![![16367388, 1642305, 2218900], ![-44298477, -5527369, 0]]]
    h := ![![![-27793, 437, -1], ![-67266, 84, 0]], ![![61749, -896, 0], ![149448, -3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N1 : Ideal.span {10} * I167N1 =  Ideal.span {B.equivFun.symm ![-77, 1, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E167RS1 


noncomputable def E181RS1 : RelationCertificate Table 500 ![![181, 0, 0], ![-29, 1, 0]]
  ![1856669, 79473, -41437] ![![500, 0, 0], ![-142, 1, 0]] where
    su := ![![90500, 0, 0], ![-14500, 500, 0]]
    hsu := by decide
    w := ![![928334500, 39736500, -20718500], ![-273840500, -11338000, 6043000]]
    hw := by decide
    g := ![![![1560411, 28910, 90365], ![-442681, -1705984, 0]], ![![-144842, 29511, -8850], ![41443, 272629, 0]]]
    h := ![![![6998048978, -241317232, 199], ![43677414081, -38728, 0]], ![![-2064305892, 71184507, -60], ![-12884097199, 11473, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R181N1 : Ideal.span {500} * I181N1 =  Ideal.span {B.equivFun.symm ![1856669, 79473, -41437]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E181RS1 


noncomputable def E191RS1 : RelationCertificate Table 500 ![![191, 0, 0], ![31, 1, 0]]
  ![5752417, 1736889, 285009] ![![500, 0, 0], ![-142, 1, 0]] where
    su := ![![95500, 0, 0], ![15500, 500, 0]]
    hsu := by decide
    w := ![![2876208500, 868444500, 142504500], ![-746731000, -225468500, -36997500]]
    hw := by decide
    g := ![![![17, 35325, -494], ![555, 125378, 0]], ![![57, 6122, -86], ![247, 21725, 0]]]
    h := ![![![34221736, 1142206, 3377], ![-210664489, -179999, 0]], ![![-8884812, -296549, -877], ![54693730, 46756, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R191N1 : Ideal.span {500} * I191N1 =  Ideal.span {B.equivFun.symm ![5752417, 1736889, 285009]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E191RS1 
