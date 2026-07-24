import IdealArithmetic.Examples.NF3_1_648324_3.PrimesBelow3_1_648324_3F4
import IdealArithmetic.Examples.NF3_1_648324_3.ClassGroupData3_1_648324_3

set_option linter.all false

noncomputable section


noncomputable def E199RS0 : RelationCertificate Table 2 ![![199, 0, 0], ![-99, 1, 0]]
  ![-7414179724, -1910164019, -257855906] ![![2, 0, 0], ![-53, -4, 1]] where
    su := ![![398, 0, 0], ![-198, 2, 0]]
    hsu := by decide
    w := ![![-14828359448, -3820328038, -515711812], ![18608117102, 4794131930, 647167060]]
    hw := by decide
    g := ![![![-573360, 2511235, -610025], ![9867919, 0, -310050]], ![![284726, -1242822, 302610], ![-4907317, 0, 154230]]]
    h := ![![![-1470852960616, 17775843833, -60461786], ![-2956488131140, 5887019754, 0]], ![![1845774256531, -22306916854, 75873528], ![3710098717082, -7387624271, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R199N0 : Ideal.span {2} * I199N0 =  Ideal.span {B.equivFun.symm ![-7414179724, -1910164019, -257855906]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E199RS0 


noncomputable def E199RS2 : RelationCertificate Table 2 ![![199, 0, 0], ![-45, 1, 0]]
  ![-776, -200, -27] ![![2, 0, 0], ![-53, -3, 1]] where
    su := ![![398, 0, 0], ![-90, 2, 0]]
    hsu := by decide
    w := ![![-1552, -400, -54], ![-9566, -2462, -332]]
    hw := by decide
    g := ![![![12, -67, 10], ![-19, 0, 0]], ![![17, 19, -3], ![5, 0, 0]]]
    h := ![![![-65054, 1509, -3], ![-287666, 285, 0]], ![![-401107, 9293, -18], ![-1773678, 1708, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R199N2 : Ideal.span {2} * I199N2 =  Ideal.span {B.equivFun.symm ![-776, -200, -27]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E199RS2 


noncomputable def E223RS1 : RelationCertificate Table 2 ![![223, 0, 0], ![33, 1, 0]]
  ![-55162851302258, -14211969181423, -1918495036483] ![![2, 0, 0], ![-53, -3, 1]] where
    su := ![![446, 0, 0], ![66, 2, 0]]
    hsu := by decide
    w := ![![-110325702604516, -28423938362846, -3836990072966], ![-678831095641250, -174891732078580, -23608897235244]]
    hw := by decide
    g := ![![![190767, 12445795, -342253], ![-23894329, 0, 0]], ![![11375, 1546114, -60215], ![-2650657, 0, 0]]]
    h := ![![![-2551075088234162, -79581079047874, -143120602295], ![17237411570451996, 14998699637651, 0]], ![![-15696696747238060, -489660249670295, -880617235794], ![106061332093523235, 92286597482220, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R223N1 : Ideal.span {2} * I223N1 =  Ideal.span {B.equivFun.symm ![-55162851302258, -14211969181423, -1918495036483]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E223RS1 


noncomputable def E227RS1 : RelationCertificate Table 2 ![![227, 0, 0], ![-91, 1, 0]]
  ![-3326744, -857091, -115700] ![![2, 0, 0], ![-53, -4, 1]] where
    su := ![![454, 0, 0], ![-182, 2, 0]]
    hsu := by decide
    w := ![![-6653488, -1714182, -231400], ![8349466, 2151128, 290384]]
    hw := by decide
    g := ![![![-697024, 3170586, -747052], ![11757207, 0, -366428]], ![![276080, -1255622, 295853], ![-4656441, 0, 145120]]]
    h := ![![![-11177962, 129650, -746], ![-27846930, 26821, 0]], ![![14027434, -162511, 932], ![34945635, -33186, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R227N1 : Ideal.span {2} * I227N1 =  Ideal.span {B.equivFun.symm ![-3326744, -857091, -115700]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E227RS1 
