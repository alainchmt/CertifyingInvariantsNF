import IdealArithmetic.Examples.NF3_1_406700_2.PrimesBelow3_1_406700_2F1
import IdealArithmetic.Examples.NF3_1_406700_2.ClassGroupData3_1_406700_2

set_option linter.all false

noncomputable section


noncomputable def E43RS1 : RelationCertificate Table 13 ![![43, 0, 0], ![-20, 1, 0]]
  ![17, 7, 1] ![![13, 0, 0], ![2, 1, 0]] where
    su := ![![559, 0, 0], ![-260, 13, 0]]
    hsu := by decide
    w := ![![221, 91, 13], ![-26, 0, 39]]
    hw := by decide
    g := ![![![-149981, -152616, -776477], ![-34809, 2018836, 0]], ![![64204, 65328, 332377], ![14904, -864178, 0]]]
    h := ![![![-17, 726, -173], ![37, 1488, 0]], ![![6, -88, 21], ![4, -180, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {13} * I43N1 =  Ideal.span {B.equivFun.symm ![17, 7, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E43RS1 


noncomputable def E47RS1 : RelationCertificate Table 3211 ![![47, 0, 0], ![8, 1, 0]]
  ![16761, -617, 651] ![![3211, 0, 0], ![-1038, 1, 0]] where
    su := ![![150917, 0, 0], ![25688, 3211, 0]]
    hsu := by decide
    w := ![![53819571, -1981187, 2090361], ![-17442152, 642200, -677521]]
    hw := by decide
    g := ![![![15959037123, -20453640852640, 98429472777], ![-11528843175, -63211407417392, 0]], ![![2806859304, -3597364563878, 17311670815], ![-2027678008, -11117554997392, 0]]]
    h := ![![![2384, 15041, 10778], ![737, -101183, 0]], ![![-776, -4875, -3493], ![-219, 32792, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {3211} * I47N1 =  Ideal.span {B.equivFun.symm ![16761, -617, 651]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E47RS1 


noncomputable def E53RS1 : RelationCertificate Table 361 ![![53, 0, 0], ![-6, 1, 0]]
  ![398, -16, 11] ![![361, 0, 0], ![-126, 1, 0]] where
    su := ![![19133, 0, 0], ![-2166, 361, 0]]
    hsu := by decide
    w := ![![143678, -5776, 3971], ![-50901, 2166, -1444]]
    hw := by decide
    g := ![![![82404482, -13383428610, 526913818], ![-65834601, -38043177660, 0]], ![![-8796959, 1428732030, -56250059], ![7028191, 4061254260, 0]]]
    h := ![![![-8350, 60150, -42993], ![2130, 455728, 0]], ![![2961, -21311, 15232], ![-731, -161460, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {361} * I53N1 =  Ideal.span {B.equivFun.symm ![398, -16, 11]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E53RS1 


noncomputable def E67RS1 : RelationCertificate Table 61009 ![![67, 0, 0], ![-13, 1, 0]]
  ![95530, -3376, 3765] ![![61009, 0, 0], ![-17093, 1, 0]] where
    su := ![![4087603, 0, 0], ![-793117, 61009, 0]]
    hsu := by decide
    w := ![![5828189770, -205966384, 229698885], ![-1633149921, 57714514, -64364495]]
    hw := by decide
    g := ![![![494693, -9789836360, 2863530], ![-278447, -34940220356, 0]], ![![-85031, 1792493932, -524305], ![70778, 6397464746, 0]]]
    h := ![![![-194198048163, 2939071177437, -1050102962865], ![81546952361, 14071379703144, 0]], ![![54417329724, -823573701419, 294255270385], ![-22850731161, -3943020623370, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {61009} * I67N1 =  Ideal.span {B.equivFun.symm ![95530, -3376, 3765]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E67RS1 


noncomputable def E73RS1 : RelationCertificate Table 61009 ![![73, 0, 0], ![-5, 1, 0]]
  ![3524, 486, -289] ![![61009, 0, 0], ![-17093, 1, 0]] where
    su := ![![4453657, 0, 0], ![-305045, 61009, 0]]
    hsu := by decide
    w := ![![214995716, 29650374, -17631601], ![-60215883, -8297224, 4941729]]
    hw := by decide
    g := ![![![-10891408760920053818285, 217897090911701949467412841, -63734962858388926408217], ![6623021863366198961448, 777681269805490002247782203, 0]], ![![755311737701069144874, -15111014010149270271755042, 4419976020146747687372], ![-459302029908269962684, -53931663402626585931775671, 0]]]
    h := ![![![-6141458392, 37218396930, -31025952793], ![930488916, 452978910720, 0]], ![![1720103484, -10424151739, 8689768137], ![-260611893, -126870614784, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {61009} * I73N1 =  Ideal.span {B.equivFun.symm ![3524, 486, -289]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E73RS1 


noncomputable def E79RS1 : RelationCertificate Table 247 ![![79, 0, 0], ![28, 1, 0]]
  ![-94, -41, -30] ![![247, 0, 0], ![-50, 1, 0]] where
    su := ![![19513, 0, 0], ![6916, 247, 0]]
    hsu := by decide
    w := ![![-23218, -10127, -7410], ![6669, 2717, 1235]]
    hw := by decide
    g := ![![![-570, 31767, -3115], ![325, 153856, 0]], ![![-227, 12646, -1240], ![124, 61248, 0]]]
    h := ![![![861608, 29785539, 5517440], ![682444, -87175558, 0]], ![![-247649, -8560595, -1585755], ![-196094, 25054930, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {247} * I79N1 =  Ideal.span {B.equivFun.symm ![-94, -41, -30]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E79RS1 
