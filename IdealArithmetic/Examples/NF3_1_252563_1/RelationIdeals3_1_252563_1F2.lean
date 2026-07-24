import IdealArithmetic.Examples.NF3_1_252563_1.PrimesBelow3_1_252563_1F2
import IdealArithmetic.Examples.NF3_1_252563_1.ClassGroupData3_1_252563_1

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 2 ![![83, 0, 0], ![-13, 1, 0]]
  ![-1203, -28, -31] ![![2, 0, 0], ![25, 1, 1]] where
    su := ![![166, 0, 0], ![-26, 2, 0]]
    hsu := by decide
    w := ![![-2406, -56, -62], ![-32140, -746, -828]]
    hw := by decide
    g := ![![![-6, 25, -4], ![-1, 0, 0]], ![![-24, -3, 0], ![2, 0, 0]]]
    h := ![![![-7167, 571, -2], ![-45666, 135, 0]], ![![-95826, 7508, -17], ![-610576, 997, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {2} * I83N1 =  Ideal.span {B.equivFun.symm ![-1203, -28, -31]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E83RS1 


noncomputable def E89RS1 : RelationCertificate Table 2 ![![89, 0, 0], ![28, 1, 0]]
  ![-112597, -2616, -2901] ![![2, 0, 0], ![25, 1, 1]] where
    su := ![![178, 0, 0], ![56, 2, 0]]
    hsu := by decide
    w := ![![-225194, -5232, -5802], ![-3008020, -69886, -77500]]
    hw := by decide
    g := ![![![-37, 370, 13], ![-23, 0, 0]], ![![-14, 112, 8], ![-7, 0, 0]]]
    h := ![![![-961953, -38327, -175], ![3053615, 12674, 0]], ![![-12848946, -511925, -2337], ![40787578, 169243, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {2} * I89N1 =  Ideal.span {B.equivFun.symm ![-112597, -2616, -2901]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E89RS1 


noncomputable def E101RS1 : RelationCertificate Table 2 ![![101, 0, 0], ![-42, 1, 0]]
  ![-627032909, -14568012, -16155161] ![![2, 0, 0], ![25, 1, 1]] where
    su := ![![202, 0, 0], ![-84, 2, 0]]
    hsu := by decide
    w := ![![-1254065818, -29136024, -32310322], ![-16751133780, -389183270, -431583828]]
    hw := by decide
    g := ![![![1296, -26081, -2814], ![1835, 0, 0]], ![![-597, 11823, 945], ![-811, 0, 0]]]
    h := ![![![-53711443165, 1452461564, -4300660], ![-129148303018, 418211499, 0]], ![![-717448444878, 19401196787, -57445888], ![-1725093270614, 5586242774, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {2} * I101N1 =  Ideal.span {B.equivFun.symm ![-627032909, -14568012, -16155161]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E101RS1 


noncomputable def E103RS1 : RelationCertificate Table 2 ![![103, 0, 0], ![21, 1, 0]]
  ![16909, -20295, 1712] ![![2, 0, 0], ![25, 1, 1]] where
    su := ![![206, 0, 0], ![42, 2, 0]]
    hsu := by decide
    w := ![![33818, -40590, 3424], ![-227680, 275608, -25642]]
    hw := by decide
    g := ![![![72594167, -157938975, -133657228], ![761629145, 0, 0]], ![![15436309, -33583892, -28420660], ![161951608, 0, 0]]]
    h := ![![![427852, 21185, 65], ![-2097707, -4983, 0]], ![![-2880392, -142754, -457], ![14122216, 34250, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {2} * I103N1 =  Ideal.span {B.equivFun.symm ![16909, -20295, 1712]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E103RS1 


noncomputable def E107RS0 : RelationCertificate Table 2 ![![107, 0, 0], ![-43, 1, 0]]
  ![349, 8, 9] ![![2, 0, 0], ![25, 1, 1]] where
    su := ![![214, 0, 0], ![-86, 2, 0]]
    hsu := by decide
    w := ![![698, 16, 18], ![9320, 218, 240]]
    hw := by decide
    g := ![![![-7, 22, 1], ![-1, 0, 0]], ![![-17, -10, -1], ![2, 0, 0]]]
    h := ![![![1194, -24, 0], ![2963, 9, 0]], ![![15620, -356, 1], ![38760, 13, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N0 : Ideal.span {2} * I107N0 =  Ideal.span {B.equivFun.symm ![349, 8, 9]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E107RS0 


noncomputable def E107RS1 : RelationCertificate Table 2 ![![107, 0, 0], ![-42, 1, 0]]
  ![-283738743, -6592173, -7310374] ![![2, 0, 0], ![25, 1, 1]] where
    su := ![![214, 0, 0], ![-84, 2, 0]]
    hsu := by decide
    w := ![![-567477486, -13184346, -14620748], ![-7580057720, -176109372, -195296054]]
    hw := by decide
    g := ![![![816, -19154, 739], ![1187, 0, 0]], ![![-321, 7174, -481], ![-431, 0, 0]]]
    h := ![![![-24401693649, 646719371, -1636212], ![-62159463850, 167764310, 0]], ![![-325944642752, 8638527640, -21855627], ![-830292541562, 2240904062, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {2} * I107N1 =  Ideal.span {B.equivFun.symm ![-283738743, -6592173, -7310374]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E107RS1 


noncomputable def E109RS1 : RelationCertificate Table 2 ![![109, 0, 0], ![-53, 1, 0]]
  ![64752644653, 1504414347, 1668316582] ![![2, 0, 0], ![25, 1, 1]] where
    su := ![![218, 0, 0], ![-106, 2, 0]]
    hsu := by decide
    w := ![![129505289306, 3008828694, 3336633164], ![1729861698840, 40190308396, 44568943434]]
    hw := by decide
    g := ![![![6223, -175167, 37396], ![9083, 0, 0]], ![![-2316, 71141, -20259], ![-3396, 0, 0]]]
    h := ![![![7219632413700, -156756430475, 403267197], ![14846701517899, -42287807891, 0]], ![![96435949905444, -2093867722123, 5386625382], ![198314219034792, -564857694921, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {2} * I109N1 =  Ideal.span {B.equivFun.symm ![64752644653, 1504414347, 1668316582]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E109RS1 
