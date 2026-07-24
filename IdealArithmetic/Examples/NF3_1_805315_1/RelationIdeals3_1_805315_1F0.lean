import IdealArithmetic.Examples.NF3_1_805315_1.PrimesBelow3_1_805315_1F0
import IdealArithmetic.Examples.NF3_1_805315_1.ClassGroupData3_1_805315_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 1 ![![2, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![2, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![2, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {1} * I2N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 4 ![![2, 0, 0], ![-17, 2, 1]]
  ![-9331264363461, 1687216387964, -598176436317] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![8, 0, 0], ![-68, 8, 4]]
    hsu := by decide
    w := ![![-37325057453844, 6748865551856, -2392705745268], ![131598815989740, -23794811756056, 8436081939820]]
    hw := by decide
    g := ![![![-1340025, 155708, 86226], ![38931, 1, 0]], ![![-23881293, 78832, 588340], ![19710, -9, 0]]]
    h := ![![![-61719834721, 301971447275, -569906591512], ![541636746707, 0, 0]], ![![217608698496, -1064675787128, 2009348083667], ![-1909675682379, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {4} * I2N1 =  Ideal.span {B.equivFun.symm ![-9331264363461, 1687216387964, -598176436317]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E2RS1 


noncomputable def E3RS0 : RelationCertificate Table 2 ![![3, 0, 0], ![-17, 1, 1]]
  ![361, -62, -29] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![6, 0, 0], ![-34, 2, 2]]
    hsu := by decide
    w := ![![722, -124, -58], ![6380, -484, -310]]
    hw := by decide
    g := ![![![-6739, 992, -322], ![497, -44, 0]], ![![-25825, 3634, -2288], ![1818, 253, 0]]]
    h := ![![![7, -14, -3], ![-20, 0, 0]], ![![32, -20, 9], ![-182, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {2} * I3N0 =  Ideal.span {B.equivFun.symm ![361, -62, -29]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 4 ![![3, 0, 0], ![1, 1, 0]]
  ![-394959731042473965, 71413959013969264, -25318713006227573] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![12, 0, 0], ![4, 4, 0]]
    hsu := by decide
    w := ![![-1579838924169895860, 285655836055877056, -101274852024910292], ![5570116861370066060, -1007151023196649172, 357069795069846320]]
    hw := by decide
    g := ![![![-818939137, 14734276, 24406936], ![3683570, 5, 0]], ![![-2062822144, -40358074, 34227592], ![-10089517, 4, 0]]]
    h := ![![![378133934048669218, 519448781346751195, -43797194470573606], ![-1529361533188481619, 21214574081098649, 0]], ![![-1333205663993491294, -1831446466682014938, 154417952152577090], ![5392146207322990397, -74797281538053938, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {4} * I3N1 =  Ideal.span {B.equivFun.symm ![-394959731042473965, 71413959013969264, -25318713006227573]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E3RS1 


noncomputable def E5RS0 : RelationCertificate Table 2 ![![5, 0, 0], ![-16, 1, 1]]
  ![-5637, -590, -63] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![10, 0, 0], ![-32, 2, 2]]
    hsu := by decide
    w := ![![-11274, -1180, -126], ![13860, -7928, -2950]]
    hw := by decide
    g := ![![![-4839891, 700093, -310259], ![350047, 0, 0]], ![![-12096358, 1749744, -775439], ![874873, 3, 0]]]
    h := ![![![-176017, -4558, -65935], ![549192, -43916, 0]], ![![253914, 5603, 94816], ![-792395, 63368, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {2} * I5N0 =  Ideal.span {B.equivFun.symm ![-5637, -590, -63]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 2 ![![5, 0, 0], ![-1, 1, 0]]
  ![-34440503, 21714414, 7997247] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![10, 0, 0], ![-2, 2, 0]]
    hsu := by decide
    w := ![![-68881006, 43428828, 15994494], ![-1759394340, 203199580, 108572070]]
    hw := by decide
    g := ![![![-2856824230347145, 413241376193230, -183135411315180], ![206620688096617, 0, 0]], ![![8629322943937349, -1248236853737120, 553178802504582], ![-624118426868559, -3, 0]]]
    h := ![![![-13456832037, 1142706732, -62191121], ![2919907758, 0, -318952852]], ![![-305514915896, 25865306536, -1437298181], ![66276044490, 0, -7240776940]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {2} * I5N1 =  Ideal.span {B.equivFun.symm ![-34440503, 21714414, 7997247]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 4 ![![7, 0, 0], ![2, 1, 0]]
  ![58582835261, 1687267732, -816612503] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![28, 0, 0], ![8, 4, 0]]
    hsu := by decide
    w := ![![234331341044, 6749070928, -3266450012], ![179654750660, 38221565412, 8436338660]]
    hw := by decide
    g := ![![![-44309038183933682800, 7540387688671635201, -2840410637307104091], ![1885096922167908803, 5, 0]], ![![76610323405670790435, -13037329698633231044, 4911069760207693404], ![-3259332424658307757, 2, 0]]]
    h := ![![![233536417149, 135506689245, 37686558831], ![-788086042391, -52924504864, 0]], ![![185777155181, 108236468082, 28952889695], ![-627763199301, -40112228640, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {4} * I7N0 =  Ideal.span {B.equivFun.symm ![58582835261, 1687267732, -816612503]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E7RS0 


noncomputable def E11RS0 : RelationCertificate Table 2 ![![11, 0, 0], ![-16, 0, 1]]
  ![-8913016466326695, 1611591619573584, -571364846069429] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![22, 0, 0], ![-32, 0, 2]]
    hsu := by decide
    w := ![![-17826032932653390, 3223183239147168, -1142729692138858], ![125700266135274380, -22728275690627694, 8057958097867920]]
    hw := by decide
    g := ![![![87969717, -8128207, -5430001], ![-4064103, 559, 0]], ![![53529214, 9243874, 2570686], ![4621939, -817, 0]]]
    h := ![![![-263715691781845, 146508329052144, -86102167010439], ![375758991045400, 0, 0]], ![![1859591125308978, -1033103440483077, 607149406091942], ![-2649664418077402, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {2} * I11N0 =  Ideal.span {B.equivFun.symm ![-8913016466326695, 1611591619573584, -571364846069429]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 4 ![![11, 0, 0], ![0, 1, 0]]
  ![-99, -4, 1] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![44, 0, 0], ![0, 4, 0]]
    hsu := by decide
    w := ![![-396, -16, 4], ![-220, -76, -20]]
    hw := by decide
    g := ![![![152, -27, 6], ![-5, 3, 0]], ![![-195, 32, -15], ![11, 2, 0]]]
    h := ![![![-9, -5, -19], ![9, 42, 0]], ![![-5, 17, 95], ![4, -210, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {4} * I11N1 =  Ideal.span {B.equivFun.symm ![-99, -4, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E11RS1 


noncomputable def E19RS0 : RelationCertificate Table 2 ![![19, 0, 0], ![7, 1, 0]]
  ![-1825, 330, -117] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![38, 0, 0], ![14, 2, 0]]
    hsu := by decide
    w := ![![-3650, 660, -234], ![25740, -4654, 1650]]
    hw := by decide
    g := ![![![41, -137, -933], ![-68, 375, 0]], ![![-37, -48, -369], ![-23, 150, 0]]]
    h := ![![![-11173, -1984, -268], ![30066, 995, 0]], ![![78776, 13933, 1855], ![-211982, -6884, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {2} * I19N0 =  Ideal.span {B.equivFun.symm ![-1825, 330, -117]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E19RS0 


noncomputable def E19RS1 : RelationCertificate Table 2 ![![19, 0, 0], ![-4, 1, 0]]
  ![-455200377, 105783158, 45706155] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![38, 0, 0], ![-8, 2, 0]]
    hsu := by decide
    w := ![![-910400754, 211566316, 91412310], ![-10055354100, 884648966, 528915790]]
    hw := by decide
    g := ![![![-60512403371263047, 8753156242608796, -3879119955422960], ![4376578121304400, 1275, 0]], ![![57655579140915902, -8339914866415986, 3695984544105155], ![-4169957433207993, -225, 0]]]
    h := ![![![-1193751575, 300709831, -2084215], ![-5556519887, 17061248, 0]], ![![-13108126566, 3264302326, -36321320], ![-61006681926, 190912595, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {2} * I19N1 =  Ideal.span {B.equivFun.symm ![-455200377, 105783158, 45706155]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E19RS1 


noncomputable def E23RS1 : RelationCertificate Table 2 ![![23, 0, 0], ![-3, 1, 0]]
  ![213, 0, -5] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![46, 0, 0], ![-6, 2, 0]]
    hsu := by decide
    w := ![![426, 0, -10], ![1100, 78, 0]]
    hw := by decide
    g := ![![![1521, -111, 780], ![-55, -273, 0]], ![![-1131, 200, 155], ![100, -91, 0]]]
    h := ![![![345, -112, 0], ![2574, -1, 0]], ![![878, -283, 0], ![6548, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {2} * I23N1 =  Ideal.span {B.equivFun.symm ![213, 0, -5]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E23RS1 


noncomputable def E31RS1 : RelationCertificate Table 4 ![![31, 0, 0], ![-3, 1, 0]]
  ![-66284902084853251, 11985189650191496, -4249163346609167] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![124, 0, 0], ![-12, 4, 0]]
    hsu := by decide
    w := ![![-265139608339413004, 47940758600765984, -16996653386436668], ![934815936254016740, -169027122793109264, 59925948250957480]]
    hw := by decide
    g := ![![![-547354090, -39827199, -1160437], ![-9956799, 0, 0]], ![![61205110, -14999715, -6712924], ![-3749925, -1, 0]]]
    h := ![![![-762692389024402255, 254886606150014642, -2591898960889827], ![-7859059719223872218, 15219940888195094, 0]], ![![2689062581728477727, -898666415248361118, 9138387391363815], ![27709078683173101784, -53661704413907779, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {4} * I31N1 =  Ideal.span {B.equivFun.symm ![-66284902084853251, 11985189650191496, -4249163346609167]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E31RS1 
