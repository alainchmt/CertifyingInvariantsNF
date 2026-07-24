import IdealArithmetic.Examples.NF3_1_410267_1.PrimesBelow3_1_410267_1F3
import IdealArithmetic.Examples.NF3_1_410267_1.ClassGroupData3_1_410267_1

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 16 ![![139, 0, 0], ![46, 1, 0]]
  ![-47, -2, -3] ![![16, 0, 0], ![3, 1, 0]] where
    su := ![![2224, 0, 0], ![736, 16, 0]]
    hsu := by decide
    w := ![![-752, -32, -48], ![-496, -16, -16]]
    hw := by decide
    g := ![![![-2488713, -5225308, -6593604], ![-793213, 21099533, 0]], ![![-872938, -1832823, -2312765], ![-278227, 7400848, 0]]]
    h := ![![![-1673, -45368, -4827], ![-780, 134190, 0]], ![![-1111, -29926, -3184], ![-492, 88515, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {16} * I139N1 =  Ideal.span {B.equivFun.symm ![-47, -2, -3]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E139RS1 


noncomputable def E149RS1 : RelationCertificate Table 512 ![![149, 0, 0], ![-19, 1, 0]]
  ![-331, 6, 1] ![![512, 0, 0], ![-29, 1, 0]] where
    su := ![![76288, 0, 0], ![-9728, 512, 0]]
    hsu := by decide
    w := ![![-169472, 3072, 512], ![9728, -512, 0]]
    hw := by decide
    g := ![![![13333, -187162, 33422], ![-624, -3422413, 0]], ![![-1623, 23127, -4130], ![511, 422912, 0]]]
    h := ![![![827, -7520, 2089], ![-50, -62252, 0]], ![![-29, 431, -120], ![148, 3576, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N1 : Ideal.span {512} * I149N1 =  Ideal.span {B.equivFun.symm ![-331, 6, 1]} * (J0 ^ 9) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_9 E149RS1 


noncomputable def E151RS0 : RelationCertificate Table 4 ![![151, 0, 0], ![-69, 1, 0]]
  ![-19, 2, 1] ![![4, 0, 0], ![-1, 1, 0]] where
    su := ![![604, 0, 0], ![-276, 4, 0]]
    hsu := by decide
    w := ![![-76, 8, 4], ![140, -32, 8]]
    hw := by decide
    g := ![![![209690, 12330, 555217], ![-49337, -444176, 0]], ![![-398955, -23467, -1056125], ![93875, 844901, 0]]]
    h := ![![![409, -17420, 1281], ![-226, -38686, 0]], ![![-676, 32201, -2368], ![593, 71514, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N0 : Ideal.span {4} * I151N0 =  Ideal.span {B.equivFun.symm ![-19, 2, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E151RS0 


noncomputable def E151RS1 : RelationCertificate Table 2097152 ![![151, 0, 0], ![-13, 1, 0]]
  ![-69527, 3166, -4763] ![![2097152, 0, 0], ![525283, 1, 0]] where
    su := ![![316669952, 0, 0], ![-27262976, 2097152, 0]]
    hsu := by decide
    w := ![![-145808687104, 6639583232, -9988734976], ![-36521902080, 1663041536, -2501902336]]
    hw := by decide
    g := ![![![-140040855020267189, -40353987579878403927948, -384115902824989008], ![-54318937313846371, 161109886768246269621039, 0]], ![![10868159607732955, 3131754499625399167431, 29810107481166467], ![4215533249811826, -12503265304868643720399, 0]]]
    h := ![![![16745072750880, -101548505573059, 42317711029147], ![-2114135439229, -1277994873081192, 0]], ![![4194276150199, -25435689730909, 10599665271147], ![-529544898484, -320109891188878, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N1 : Ideal.span {2097152} * I151N1 =  Ideal.span {B.equivFun.symm ![-69527, 3166, -4763]} * (J0 ^ 21) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_21 E151RS1 


noncomputable def E157RS1 : RelationCertificate Table 1024 ![![157, 0, 0], ![77, 1, 0]]
  ![-57, 66, 11] ![![1024, 0, 0], ![-29, 1, 0]] where
    su := ![![160768, 0, 0], ![78848, 1024, 0]]
    hsu := by decide
    w := ![![-58368, 67584, 11264], ![3072, -2048, 0]]
    hw := by decide
    g := ![![![-153518663863109, 2151811953786423, -384253259234217], ![6449075396947, 78695067491167646, 0]], ![![-74803701696236, 1048494661476440, -187231737537781], ![3142384776873, 38345059847737551, 0]]]
    h := ![![![8686542, 478515633, 30677063], ![7308213, -963259776, 0]], ![![-455089, -25067386, -1607040], ![-382768, 50461056, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N1 : Ideal.span {1024} * I157N1 =  Ideal.span {B.equivFun.symm ![-57, 66, 11]} * (J0 ^ 10) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_10 E157RS1 


noncomputable def E167RS1 : RelationCertificate Table 4 ![![167, 0, 0], ![64, 1, 0]]
  ![9, -2, 1] ![![4, 0, 0], ![-1, 1, 0]] where
    su := ![![668, 0, 0], ![256, 4, 0]]
    hsu := by decide
    w := ![![36, -8, 4], ![104, -4, -12]]
    hw := by decide
    g := ![![![-104, -4, -367], ![28, 295, 0]], ![![-39, -2, -143], ![13, 115, 0]]]
    h := ![![![-5683, -226466, -17422], ![-3355, 581895, 0]], ![![-16272, -653112, -50244], ![-9982, 1678149, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N1 : Ideal.span {4} * I167N1 =  Ideal.span {B.equivFun.symm ![9, -2, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E167RS1 
