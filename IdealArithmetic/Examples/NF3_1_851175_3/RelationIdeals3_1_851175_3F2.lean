import IdealArithmetic.Examples.NF3_1_851175_3.PrimesBelow3_1_851175_3F2
import IdealArithmetic.Examples.NF3_1_851175_3.ClassGroupData3_1_851175_3

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 7 ![![83, 0, 0], ![-18, 1, 0]]
  ![-127708, -4473, -3400] ![![7, 0, 0], ![1, 1, 0]] where
    su := ![![581, 0, 0], ![-126, 7, 0]]
    hsu := by decide
    w := ![![-893956, -31311, -23800], ![-504035, -17654, -13419]]
    hw := by decide
    g := ![![![151, -176, -205], ![1, 498, 0]], ![![-22, 35, 44], ![5, -110, 0]]]
    h := ![![![491988, 8409758, -1484114], ![-5369, 41059354, 0]], ![![277399, 4741634, -836781], ![-3010, 23150302, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {7} * I83N1 =  Ideal.span {B.equivFun.symm ![-127708, -4473, -3400]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E83RS1 


noncomputable def E89RS0 : RelationCertificate Table 49 ![![89, 0, 0], ![-41, 1, 0]]
  ![1428, -1127, 843] ![![49, 0, 0], ![1, 1, 0]] where
    su := ![![4361, 0, 0], ![-2009, 49, 0]]
    hsu := by decide
    w := ![![69972, -55223, 41307], ![96971, -30331, -3381]]
    hw := by decide
    g := ![![![886051874, -1770063875, -2655660000], ![-18041042, 43375979860, 0]], ![![-410156085, 819400917, 1229362140], ![8351949, -20079667073, 0]]]
    h := ![![![7302, 292034, -21894], ![-33, 649803, 0]], ![![9779, 390743, -29307], ![-26, 869418, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N0 : Ideal.span {49} * I89N0 =  Ideal.span {B.equivFun.symm ![1428, -1127, 843]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E89RS0 


noncomputable def E89RS1 : RelationCertificate Table 49 ![![89, 0, 0], ![-30, 1, 0]]
  ![-131502, -4606, -3501] ![![49, 0, 0], ![1, 1, 0]] where
    su := ![![4361, 0, 0], ![-1470, 49, 0]]
    hsu := by decide
    w := ![![-6443598, -225694, -171549], ![-519008, -18179, -13818]]
    hw := by decide
    g := ![![![121479, -242837, -364341], ![-2462, 5950896, 0]], ![![-40998, 81952, 122958], ![863, -2008308, 0]]]
    h := ![![![3163342, 92088059, -9526359], ![-31507, 282614150, 0]], ![![254817, 7417352, -767313], ![-2474, 22763525, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {49} * I89N1 =  Ideal.span {B.equivFun.symm ![-131502, -4606, -3501]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E89RS1 


noncomputable def E89RS2 : RelationCertificate Table 49 ![![89, 0, 0], ![-18, 1, 0]]
  ![-51758, -1813, -1378] ![![49, 0, 0], ![1, 1, 0]] where
    su := ![![4361, 0, 0], ![-882, 49, 0]]
    hsu := by decide
    w := ![![-2536142, -88837, -67522], ![-204281, -7154, -5439]]
    hw := by decide
    g := ![![![284008415963, -567662412109, -851670828076], ![-5788857038, 13910623525223, 0]], ![![-58078120847, 116083764835, 174161885681], ![1183788663, -2844644132785, 0]]]
    h := ![![![194346, 3320433, -585974], ![-1938, 17383436, 0]], ![![15655, 267454, -47199], ![-152, 1400200, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N2 : Ideal.span {49} * I89N2 =  Ideal.span {B.equivFun.symm ![-51758, -1813, -1378]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E89RS2 


noncomputable def E101RS1 : RelationCertificate Table 49 ![![101, 0, 0], ![-17, 1, 0]]
  ![-2821, -98, -75] ![![49, 0, 0], ![1, 1, 0]] where
    su := ![![4949, 0, 0], ![-833, 49, 0]]
    hsu := by decide
    w := ![![-138229, -4802, -3675], ![-11123, -392, -294]]
    hw := by decide
    g := ![![![15042286, -30065800, -45108084], ![-306581, 736765376, 0]], ![![-2561657, 5120116, 7681773], ![52237, -125468960, 0]]]
    h := ![![![13044755, 209056392, -39197841], ![-125738, 1319660622, 0]], ![![1049692, 16822243, -3154152], ![-10039, 106189782, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {49} * I101N1 =  Ideal.span {B.equivFun.symm ![-2821, -98, -75]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E101RS1 


noncomputable def E103RS0 : RelationCertificate Table 49 ![![103, 0, 0], ![43, 1, 0]]
  ![25681208, 899493, 683717] ![![49, 0, 0], ![1, 1, 0]] where
    su := ![![5047, 0, 0], ![2107, 49, 0]]
    hsu := by decide
    w := ![![1258379192, 44075157, 33502133], ![101358019, 3550099, 2698479]]
    hw := by decide
    g := ![![![-1933278608051, 3864144638842, 5797423246858], ![39405429211, -94691246365802, 0]], ![![-803342955610, 1605683403335, 2409026358891], ![16374294883, -39347430528730, 0]]]
    h := ![![![-137490971, 6038099828, 411695477], ![1223281, -14134650138, 0]], ![![-11074413, 486347709, 33160623], ![98528, -1138496366, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N0 : Ideal.span {49} * I103N0 =  Ideal.span {B.equivFun.symm ![25681208, 899493, 683717]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E103RS0 


noncomputable def E103RS2 : RelationCertificate Table 7 ![![103, 0, 0], ![-9, 1, 0]]
  ![1907619, 66815, 50787] ![![7, 0, 0], ![1, 1, 0]] where
    su := ![![721, 0, 0], ![-63, 7, 0]]
    hsu := by decide
    w := ![![13353333, 467705, 355509], ![7528948, 263704, 200445]]
    hw := by decide
    g := ![![![274, 9, 84], ![43, -309, 0]], ![![-76, 18, -9], ![-3, 27, 0]]]
    h := ![![![-1052084145, -8424009538, 3158967384], ![10143189, -108457863255, 0]], ![![-593191730, -4749670346, 1781105973], ![5719086, -61151295528, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N2 : Ideal.span {7} * I103N2 =  Ideal.span {B.equivFun.symm ![1907619, 66815, 50787]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E103RS2 


noncomputable def E109RS1 : RelationCertificate Table 49 ![![109, 0, 0], ![-52, 1, 0]]
  ![812, -98, -233] ![![49, 0, 0], ![1, 1, 0]] where
    su := ![![5341, 0, 0], ![-2548, 49, 0]]
    hsu := by decide
    w := ![![39788, -4802, -11417], ![-25186, 8771, -294]]
    hw := by decide
    g := ![![![46862860, -93733136, -140628145], ![-956519, 2296912270, 0]], ![![-22787701, 45576617, 68378786], ![465128, -1116847160, 0]]]
    h := ![![![1739092, 89009651, -5235857], ![-12997, 190236060, 0]], ![![-1106488, -56634148, 3331416], ![8361, -121041450, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {49} * I109N1 =  Ideal.span {B.equivFun.symm ![812, -98, -233]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E109RS1 


noncomputable def E113RS1 : RelationCertificate Table 49 ![![113, 0, 0], ![-8, 1, 0]]
  ![-56, 0, -3] ![![49, 0, 0], ![1, 1, 0]] where
    su := ![![5537, 0, 0], ![-392, 49, 0]]
    hsu := by decide
    w := ![![-2744, 0, -147], ![-392, 49, 0]]
    hw := by decide
    g := ![![![1012, -2026, -3039], ![-7, 49636, 0]], ![![-74, 145, 219], ![50, -3577, 0]]]
    h := ![![![38288, 268137, -114915], ![-233, 4328464, 0]], ![![5521, 38647, -16563], ![1, 623873, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {49} * I113N1 =  Ideal.span {B.equivFun.symm ![-56, 0, -3]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E113RS1 
