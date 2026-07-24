import IdealArithmetic.Examples.NF3_1_866700_5.PrimesBelow3_1_866700_5F3
import IdealArithmetic.Examples.NF3_1_866700_5.ClassGroupData3_1_866700_5

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 13 ![![139, 0, 0], ![20, 1, 0]]
  ![515, -3, -52] ![![13, 0, 0], ![1, 1, 0]] where
    su := ![![1807, 0, 0], ![260, 13, 0]]
    hsu := by decide
    w := ![![6695, -39, -676], ![-8931, 494, 221]]
    hw := by decide
    g := ![![![75927, -221, -1900], ![5836, 0, -5325]], ![![11634, -13, -273], ![894, 0, -804]]]
    h := ![![![-269755, 1188002, 593892], ![-30201, -6350080, 0]], ![![362367, -1595967, -797837], ![40731, 8530720, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {13} * I139N1 =  Ideal.span {B.equivFun.symm ![515, -3, -52]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E139RS1 


noncomputable def E157RS1 : RelationCertificate Table 49 ![![157, 0, 0], ![-5, 1, 0]]
  ![63, 7, -18] ![![49, 0, 0], ![-8, 1, 0]] where
    su := ![![7693, 0, 0], ![-245, 49, 0]]
    hsu := by decide
    w := ![![3087, 343, -882], ![-3822, 49, 343]]
    hw := by decide
    g := ![![![-629559409, -217212829, 1398836639], ![98352304, -5272538106, 0]], ![![20717985, 7148192, -46033900], ![-3236630, 173512392, 0]]]
    h := ![![![1134, -189, -2449], ![105, 29575, 0]], ![![-1399, 233, 3036], ![85, -36665, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N1 : Ideal.span {49} * I157N1 =  Ideal.span {B.equivFun.symm ![63, 7, -18]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E157RS1 


noncomputable def E163RS1 : RelationCertificate Table 8281 ![![163, 0, 0], ![-61, 1, 0]]
  ![567, -133, 195] ![![8281, 0, 0], ![1119, 1, 0]] where
    su := ![![1349803, 0, 0], ![-505141, 8281, 0]]
    hsu := by decide
    w := ![![4695327, -1101373, 1614795], ![670761, -149058, 215306]]
    hw := by decide
    g := ![![![-25422991465197218943, 4839046389397430882615, 55917865408019566060], ![-2851018121018983460, -35619680266295114773290, 16196285274]], ![![9309827860495055789, -1772045156680806594700, -20476964797303601325], ![1044034804880234170, 13043826576390181804868, -5931034044]]]
    h := ![![![10829, 110299, -26065], ![-3220, 326830, 0]], ![![1568, 15733, -3718], ![-397, 46620, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N1 : Ideal.span {8281} * I163N1 =  Ideal.span {B.equivFun.symm ![567, -133, 195]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E163RS1 


noncomputable def E163RS2 : RelationCertificate Table 91 ![![163, 0, 0], ![-10, 1, 0]]
  ![-25011, -3122, -2028] ![![91, 0, 0], ![27, 1, 0]] where
    su := ![![14833, 0, 0], ![-910, 91, 0]]
    hsu := by decide
    w := ![![-2276001, -284102, -184548], ![-1025661, -128037, -83174]]
    hw := by decide
    g := ![![![171824923764607, -1010551515049596, -397923506733307], ![39876059632974, 2785463994238800, 342267925]], ![![-10357896812829, 60917753301350, 23987501532565], ![-2403796270775, -167912477398548, -20632489]]]
    h := ![![![-6686373, -4475508, 14537692], ![382890, -182280448, 0]], ![![-3013153, -2016851, 6551290], ![172634, -82143168, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N2 : Ideal.span {91} * I163N2 =  Ideal.span {B.equivFun.symm ![-25011, -3122, -2028]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E163RS2 


noncomputable def E167RS1 : RelationCertificate Table 13 ![![167, 0, 0], ![40, 1, 0]]
  ![47, -3, 0] ![![13, 0, 0], ![1, 1, 0]] where
    su := ![![2171, 0, 0], ![520, 13, 0]]
    hsu := by decide
    w := ![![611, -39, 0], ![65, 26, -39]]
    hw := by decide
    g := ![![![844907276, -4970042, -23348277], ![64610561, 0, -60705522]], ![![205040260, -1206119, -5666109], ![15679552, 0, -14731884]]]
    h := ![![![246441, -1976443, -558480], ![47258, 7174320, 0]], ![![26027, -208888, -59025], ![5074, 758244, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N1 : Ideal.span {13} * I167N1 =  Ideal.span {B.equivFun.symm ![47, -3, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E167RS1 


noncomputable def E173RS1 : RelationCertificate Table 7 ![![173, 0, 0], ![-84, 1, 0]]
  ![35, 0, -4] ![![7, 0, 0], ![-1, 1, 0]] where
    su := ![![1211, 0, 0], ![-588, 7, 0]]
    hsu := by decide
    w := ![![245, 0, -28], ![-763, 35, 28]]
    hw := by decide
    g := ![![![-27482, 22697, 61684], ![7169, -33216, 0]], ![![13381, -11054, -30040], ![-3489, 16176, 0]]]
    h := ![![![-41783, -647958, 107977], ![16584, -1436925, 0]], ![![130387, 2020570, -336712], ![-51525, 4480860, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R173N1 : Ideal.span {7} * I173N1 =  Ideal.span {B.equivFun.symm ![35, 0, -4]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E173RS1 


noncomputable def E179RS1 : RelationCertificate Table 91 ![![179, 0, 0], ![14, 1, 0]]
  ![133, 7, -26] ![![91, 0, 0], ![27, 1, 0]] where
    su := ![![16289, 0, 0], ![1274, 91, 0]]
    hsu := by decide
    w := ![![12103, 637, -2366], ![-1183, 364, -455]]
    hw := by decide
    g := ![![![10185693, -59811269, -23549778], ![2364916, 164862438, -8665]], ![![828700, -4866350, -1916051], ![192498, 13413495, -705]]]
    h := ![![![9919, -33264, -21619], ![763, 297675, 0]], ![![-985, 3269, 2125], ![53, -29260, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N1 : Ideal.span {91} * I179N1 =  Ideal.span {B.equivFun.symm ![133, 7, -26]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E179RS1 


noncomputable def E191RS1 : RelationCertificate Table 7 ![![191, 0, 0], ![61, 1, 0]]
  ![-21, 0, 1] ![![7, 0, 0], ![-1, 1, 0]] where
    su := ![![1337, 0, 0], ![427, 7, 0]]
    hsu := by decide
    w := ![![-147, 0, 7], ![203, -21, -7]]
    hw := by decide
    g := ![![![1886, -1567, -4257], ![-493, 2292, 0]], ![![600, -499, -1354], ![-153, 729, 0]]]
    h := ![![![-93766, 1132709, 219755], ![-23983, -3228708, 0]], ![![129538, -1565578, -303735], ![33339, 4462568, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R191N1 : Ideal.span {7} * I191N1 =  Ideal.span {B.equivFun.symm ![-21, 0, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E191RS1 


noncomputable def E193RS0 : RelationCertificate Table 13 ![![193, 0, 0], ![58, 1, 0]]
  ![1921, 240, 156] ![![13, 0, 0], ![1, 1, 0]] where
    su := ![![2509, 0, 0], ![754, 13, 0]]
    hsu := by decide
    w := ![![24973, 3120, 2028], ![28873, 3601, 2340]]
    hw := by decide
    g := ![![![59053, -344, -1634], ![4520, 0, -4246]], ![![17717, -104, -490], ![1365, 0, -1274]]]
    h := ![![![-1371939, 15696688, 3188042], ![-330944, -47330150, 0]], ![![-1586247, 18148416, 3685995], ![-382571, -54722835, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R193N0 : Ideal.span {13} * I193N0 =  Ideal.span {B.equivFun.symm ![1921, 240, 156]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E193RS0 


noncomputable def E193RS1 : RelationCertificate Table 13 ![![193, 0, 0], ![-33, 1, 0]]
  ![-33, 1, 0] ![![13, 0, 0], ![1, 1, 0]] where
    su := ![![2509, 0, 0], ![-429, 13, 0]]
    hsu := by decide
    w := ![![-429, 13, 0], ![-39, -26, 13]]
    hw := by decide
    g := ![![![-957241560, 5630832, 26452538], ![-73200819, 0, 68776599]], ![![159313317, -937138, -4402485], ![12182794, 0, -11446461]]]
    h := ![![![-190215, -877645, 422500], ![27986, -6272500, 0]], ![![-17118, -79055, 38057], ![2613, -565000, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R193N1 : Ideal.span {13} * I193N1 =  Ideal.span {B.equivFun.symm ![-33, 1, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E193RS1 


noncomputable def E193RS2 : RelationCertificate Table 13 ![![193, 0, 0], ![-25, 1, 0]]
  ![15069, 1881, 1222] ![![13, 0, 0], ![1, 1, 0]] where
    su := ![![2509, 0, 0], ![-325, 13, 0]]
    hsu := by decide
    w := ![![195897, 24453, 15886], ![226187, 28236, 18343]]
    hw := by decide
    g := ![![![22388, -140, -621], ![1717, 0, -1596]], ![![-2034, 13, 56], ![-147, 0, 144]]]
    h := ![![![60396528, 194087322, -132772406], ![-6817725, 1971159660, 0]], ![![69735167, 224097468, -153301925], ![-7871784, 2275944072, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R193N2 : Ideal.span {13} * I193N2 =  Ideal.span {B.equivFun.symm ![15069, 1881, 1222]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E193RS2 
