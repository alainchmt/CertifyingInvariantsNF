
import IdealArithmetic.Examples.NF3_1_304556_1.RI3_1_304556_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0]] 
 ![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [19, 29, 26, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 8, 23], [14, 28, 14], [0, 1]]
 g := ![![[6, 35, 1], [30, 30], [16, 17, 28], [11, 1], []], ![[26, 4, 26, 29], [7, 1], [32, 24, 5, 15], [36, 7], [8, 11]], ![[27, 17, 19, 24], [25, 28], [14, 2], [18, 27], [17, 11]]]
 h' := ![![[34, 8, 23], [12, 12, 1], [29, 11, 20], [13, 32, 18], [0, 0, 1], [0, 1]], ![[14, 28, 14], [18, 14, 8], [22, 2, 36], [7, 1, 19], [5, 29, 28], [34, 8, 23]], ![[0, 1], [16, 11, 28], [11, 24, 18], [25, 4], [21, 8, 8], [14, 28, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 30], []]
 b := ![[], [9, 0, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [19, 29, 26, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-169090, -34595, -9879]
  a := ![-1, -1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4570, -935, -267]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def PBC37 : ContainsPrimesAboveP 37 ![I37N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![37, 0, 0]]) timesTableT_eq_Table B_one_repr 37 (by decide) 𝕀

instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-337172294274317, 94713176390268, -18798786337250]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-337172294274317, 94713176390268, -18798786337250]] 
 ![![41, 0, 0], ![6, 1, 0], ![2, 0, 1]] where
  M :=![![![-337172294274317, 94713176390268, -18798786337250], ![-1973153320707232, -637952875670317, 265340742833554], ![9628900376764980, 725861796079788, -543239699280049]]]
  hmulB := by decide  
  f := ![![![-153960620167676852500991998981, -37806636645230960918973660132, -13138524776558636576693044222]], ![![-58702636172505904862467329718, -14415044791804897640046894325, -5009502033453739970579811950]], ![![-122401690534785905910004743166, -30057012200722439823478871700, -10445382994901543214644889149]]]
  g := ![![![-21167165364425, 94713176390268, -18798786337250], ![32289815796282, -637952875670317, 265340742833554], ![155127048752350, 725861796079788, -543239699280049]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-380244257433, -93372944728, -32448872913]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-380244257433, -93372944728, -32448872913]] 
 ![![41, 0, 0], ![14, 1, 0], ![17, 0, 1]] where
  M :=![![![-380244257433, -93372944728, -32448872913], ![-3662748965158, -899426224041, -312567707097], ![-11633876582426, -2856819777994, -992799168769]]]
  hmulB := by decide  
  f := ![![![-5952111, 723310, -33183]], ![![-2103814, 88861, 40785]], ![![-561353, 548184, -154240]]]
  g := ![![![36063605080, -93372944728, -32448872913], ![347387053465, -899426224041, -312567707097], ![1103394784843, -2856819777994, -992799168769]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5691699263756335776562496164, -1860411970244046961912536777, 771751179862151437917128205]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![-5691699263756335776562496164, -1860411970244046961912536777, 771751179862151437917128205]] 
 ![![41, 0, 0], ![20, 1, 0], ![31, 0, 1]] where
  M :=![![![-5691699263756335776562496164, -1860411970244046961912536777, 771751179862151437917128205], ![83032217814592611208971565773, 6656319614038087230111555116, -4809484730869989447820482126], ![-172231767172634805417859660860, 2646958030305609001918796178, 4795907643794040268199018339]]]
  hmulB := by decide  
  f := ![![![44653598346509987734810454630073125554902329105379386752, 10965156971633305569178626631389329286501200449124953893, 3810600448343022722210113164565365112593497334550501122]], ![![32273248127306477066060979691098585433410548520908971033, 7925032803723523479847434094900135441132251108309426404, 2754099520246424240828006252440015981072366960315497201]], ![![67084732547606833822477994534069230449903198529795779626, 16473356012126154050834639136269361248645934369755948295, 5724804302201594176777180487708161344714583031179948619]]]
  g := ![![![185176916229217289908713781, -1860411970244046961912536777, 771751179862151437917128205], ![2414630541239037548516473399, 6656319614038087230111555116, -4809484730869989447820482126], ![-9118147920399078872448906169, 2646958030305609001918796178, 4795907643794040268199018339]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-337172294274317, 94713176390268, -18798786337250]] ![![-380244257433, -93372944728, -32448872913]]
  ![![2585134417, -296605712, 8888675]] where
 M := ![![![2585134417, -296605712, 8888675]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![2585134417, -296605712, 8888675]] ![![-5691699263756335776562496164, -1860411970244046961912536777, 771751179862151437917128205]]
  ![![41, 0, 0]] where
 M := ![![![-40872549944859609434423916559837132264, -6760189482827971039514602054991892451, 3464230443750527588309821775046846022]]]
 hmul := by decide  
 g := ![![![![-996891462069746571571315038044808104, -164882670312877342427185415975412011, 84493425457329941178288335976752342]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1, I41N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
    exact isPrimeI41N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0 ⊙ MulI41N1)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0]] 
 ![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [10, 1, 30, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 30, 21], [32, 12, 22], [0, 1]]
 g := ![![[32, 36, 15], [29, 35, 41], [5, 35], [39, 13, 1], []], ![[29, 31, 6, 16], [25, 8, 0, 23], [8, 13], [39, 33, 3, 14], [27, 11]], ![[29, 39, 11, 7], [39, 42, 13, 12], [30, 38], [25, 40, 6, 20], [26, 11]]]
 h' := ![![[24, 30, 21], [11, 12, 31], [2, 14, 16], [40, 3, 11], [0, 0, 1], [0, 1]], ![[32, 12, 22], [24, 32, 22], [31, 26, 13], [38, 18, 23], [5, 13, 12], [24, 30, 21]], ![[0, 1], [42, 42, 33], [32, 3, 14], [26, 22, 9], [33, 30, 30], [32, 12, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30, 38], []]
 b := ![[], [18, 40, 33], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [10, 1, 30, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1256804, 441266, 107543]
  a := ![2, -2, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![29228, 10262, 2501]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def PBC43 : ContainsPrimesAboveP 43 ![I43N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![43, 0, 0]]) timesTableT_eq_Table B_one_repr 43 (by decide) 𝕀

instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61806331789, -18853803252, 3915740836]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![61806331789, -18853803252, 3915740836]] 
 ![![47, 0, 0], ![0, 1, 0], ![16, 0, 1]] where
  M :=![![![61806331789, -18853803252, 3915740836], ![411877688708, 124458185165, -52645668920], ![-1909457242608, -137199736920, 105604381913]]]
  hmulB := by decide  
  f := ![![![-5920357792562110394245, -1453805626590668515956, -505225085862571429900]], ![![-1213373724924968634148, -297956578007728793035, -103545573736905893144]], ![![-5869442493876495811040, -1441302843768710480136, -500880131207554567383]]]
  g := ![![![-17989821, -18853803252, 3915740836], ![26685284924, 124458185165, -52645668920], ![-76577177728, -137199736920, 105604381913]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1287935577271047, -316266018799624, -109908452396190]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-1287935577271047, -316266018799624, -109908452396190]] 
 ![![47, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![-1287935577271047, -316266018799624, -109908452396190], ![-12406195782380524, -3046470815610087, -1058706508795062], ![-39405417068598620, -9676411301433964, -3362736834409711]]]
  hmulB := by decide  
  f := ![![![-580069089, -21448496, 25711842]], ![![47378405, -4045279, -274932]], ![![-27222068, 15674924, -4045279]]]
  g := ![![![-20673820393009, -316266018799624, -109908452396190], ![-199143084399371, -3046470815610087, -1058706508795062], ![-632532037599248, -9676411301433964, -3362736834409711]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![769163, 188876, 65638]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![769163, 188876, 65638]] 
 ![![47, 0, 0], ![45, 1, 0], ![46, 0, 1]] where
  M :=![![![769163, 188876, 65638], ![7409056, 1819371, 632266], ![23533156, 5778812, 2008247]]]
  hmulB := by decide  
  f := ![![![4645, 1684, -682]], ![![2887, 1479, -560]], ![![7878, 1612, -765]]]
  g := ![![![-228715, 188876, 65638], ![-2203125, 1819371, 632266], ![-6997718, 5778812, 2008247]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![61806331789, -18853803252, 3915740836]] ![![-1287935577271047, -316266018799624, -109908452396190]]
  ![![4645, 1684, -682]] where
 M := ![![![4645, 1684, -682]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![4645, 1684, -682]] ![![769163, 188876, 65638]]
  ![![47, 0, 0]] where
 M := ![![![47, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1, I47N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
    exact isPrimeI47N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0 ⊙ MulI47N1)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![443866613365566068, 9603290941611423, -17530886915637082]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![443866613365566068, 9603290941611423, -17530886915637082]] 
 ![![53, 0, 0], ![0, 53, 0], ![41, 1, 1]] where
  M :=![![![443866613365566068, 9603290941611423, -17530886915637082], ![-1918794269778467597, 163372422715372756, 11278985909197187], ![320064753120499086, -582644595390974676, 172975713656984179]]]
  hmulB := by decide  
  f := ![![![-657190596085788588584648101642712, -161380007730668154025723033808655, -56082619829607827796558205373681]], ![![-6330468188987529211647125624913565, -1554512513359513833329579387621608, -540222643021612289873727306799646]], ![![-1007217990787205416111371247866253, -247332886544360893967004470573765, -85952878813692739941281436765110]]]
  g := ![![![21936471262390310, 511965619948085, -17530886915637082], ![-44928918718029288, 2869687486908973, 11278985909197187], ![-127772443524827401, -14256986963169035, 172975713656984179]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [49, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [40, 52], [0, 1]]
 g := ![![[10, 13], [38], [35, 46], [37], [40, 1]], ![[0, 40], [38], [20, 7], [37], [27, 52]]]
 h' := ![![[40, 52], [36, 15], [34, 41], [43, 24], [1, 14], [0, 1]], ![[0, 1], [0, 38], [31, 12], [49, 29], [31, 39], [40, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [26, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [49, 13, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![695372, 716453, 289644]
  a := ![-65, 1, -131]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-210944, 8053, 289644]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![657190596085788588584648101642712, 161380007730668154025723033808655, 56082619829607827796558205373681]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![657190596085788588584648101642712, 161380007730668154025723033808655, 56082619829607827796558205373681]] 
 ![![53, 0, 0], ![49, 1, 0], ![48, 0, 1]] where
  M :=![![![657190596085788588584648101642712, 161380007730668154025723033808655, 56082619829607827796558205373681], ![6330468188987529211647125624913565, 1554512513359513833329579387621608, 540222643021612289873727306799646], ![20107270883217025710284978344646652, 4937550156534219231867013166633082, 1715892521090181987355302421430263]]]
  hmulB := by decide  
  f := ![![![-443866613365566068, -9603290941611423, 17530886915637082]], ![![-374163580851589995, -11961012808572311, 15994990055792827]], ![![-408031362163540950, 2295974154596724, 12613336948935769]]]
  g := ![![![-187592368576191069677558007790907, 161380007730668154025723033808655, 56082619829607827796558205373681], ![-1807006260955962991234739152734495, 1554512513359513833329579387621608, 540222643021612289873727306799646], ![-5739538260363933057438739302811830, 4937550156534219231867013166633082, 1715892521090181987355302421430263]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![443866613365566068, 9603290941611423, -17530886915637082]] ![![657190596085788588584648101642712, 161380007730668154025723033808655, 56082619829607827796558205373681]]
  ![![53, 0, 0]] where
 M := ![![![-53, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-46578, -32689, 11814]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-46578, -32689, 11814]] 
 ![![59, 0, 0], ![0, 59, 0], ![36, 4, 1]] where
  M :=![![![-46578, -32689, 11814], ![1266851, 142446, -86253], ![-3099602, -26836, 109757]]]
  hmulB := by decide  
  f := ![![![225758646, 55437391, 19265547]], ![![2174647561, 534007398, 185577720]], ![![402257076, 98778422, 34327379]]]
  g := ![![![-7998, -1355, 11814], ![74101, 8262, -86253], ![-119506, -7896, 109757]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [56, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [34, 58], [0, 1]]
 g := ![![[31, 19], [58, 27], [12], [31, 28], [34, 1]], ![[28, 40], [32, 32], [12], [39, 31], [9, 58]]]
 h' := ![![[34, 58], [56, 14], [12, 33], [34, 37], [43, 38], [0, 1]], ![[0, 1], [1, 45], [13, 26], [53, 22], [37, 21], [34, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [7, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [56, 25, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![529, 1855, 626]
  a := ![-2, 1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-373, -11, 626]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-225758646, -55437391, -19265547]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-225758646, -55437391, -19265547]] 
 ![![59, 0, 0], ![46, 1, 0], ![3, 0, 1]] where
  M :=![![![-225758646, -55437391, -19265547], ![-2174647561, -534007398, -185577720], ![-6907265984, -1696151230, -589444789]]]
  hmulB := by decide  
  f := ![![![46578, 32689, -11814]], ![![14843, 23072, -7749]], ![![54904, 2117, -2461]]]
  g := ![![![40375559, -55437391, -19265547], ![388922473, -534007398, -185577720], ![1235322457, -1696151230, -589444789]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-46578, -32689, 11814]] ![![-225758646, -55437391, -19265547]]
  ![![59, 0, 0]] where
 M := ![![![-59, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![28078821644753661872370802, 6895047617977299604053213, 2396160092589821548614985]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![28078821644753661872370802, 6895047617977299604053213, 2396160092589821548614985]] 
 ![![61, 0, 0], ![0, 61, 0], ![8, 23, 1]] where
  M :=![![![28078821644753661872370802, 6895047617977299604053213, 2396160092589821548614985], ![270472657802857669951701563, 66417383126190806650210562, 23081302946521720360774624], ![859093961866275461487682800, 210959485776409298706680778, 73312430744168106254263775]]]
  hmulB := by decide  
  f := ![![![-9694916917802, -1151160918045, 679296354022]], ![![73571438024375, 1173824746550, -2774186400113]], ![![24860434182003, 457386131254, -956545123638]]]
  g := ![![![146058047607132614482802, -790436631337517967444122, 2396160092589821548614985], ![1406921872634162410909911, -7613976797439487895862390, 23081302946521720360774624], ![4468762555949682154976600, -24184039694089461395760427, 73312430744168106254263775]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [2, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 60], [0, 1]]
 g := ![![[5, 39], [16], [17, 56], [51, 27], [51, 1]], ![[42, 22], [16], [6, 5], [25, 34], [41, 60]]]
 h' := ![![[51, 60], [26, 51], [27, 57], [20, 19], [20, 37], [0, 1]], ![[0, 1], [4, 10], [6, 4], [13, 42], [16, 24], [51, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53]]
 b := ![[], [41, 57]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [2, 10, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1032, 466, 129]
  a := ![-1, -1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![0, -41, 129]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![160300590338236517376483915345658222115183093487, 39363482469305358670602888244374451680675685850, 13679558289399920571616833358520887996106282274]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![160300590338236517376483915345658222115183093487, 39363482469305358670602888244374451680675685850, 13679558289399920571616833358520887996106282274]] 
 ![![61, 0, 0], ![52, 1, 0], ![14, 0, 1]] where
  M :=![![![160300590338236517376483915345658222115183093487, 39363482469305358670602888244374451680675685850, 13679558289399920571616833358520887996106282274], ![1544114894303296621548454557681672131252366735990, 379173522968635246522353249081992430052883609871, 131770005697315996583425498091644243038133339824], ![4904524519778386117774224707939066980710789299008, 1204357167663682402737553212967868522727274829108, 418537005437940605192956137326366881733559295721]]]
  hmulB := by decide  
  f := ![![![6988996674417337992864999, -148014550709306085616258, -181829822006378100436254]], ![![5627516919644109483530750, -59295690402764394527221, -165262692105999304589676]], ![![1211926235074609545311458, -197988345008968242406728, 22722745303552276953461]]]
  g := ![![![-34067447772413787237663966235755831102056402009, 39363482469305358670602888244374451680675685850, 13679558289399920571616833358520887996106282274], ![-328158825898822297537407727342048420230023733358, 379173522968635246522353249081992430052883609871, 131770005697315996583425498091644243038133339824], ![-1042320758604332250775080791622282500743890687782, 1204357167663682402737553212967868522727274829108, 418537005437940605192956137326366881733559295721]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![28078821644753661872370802, 6895047617977299604053213, 2396160092589821548614985]] ![![160300590338236517376483915345658222115183093487, 39363482469305358670602888244374451680675685850, 13679558289399920571616833358520887996106282274]]
  ![![61, 0, 0]] where
 M := ![![![26899823336926508115478824403296220489681566601215834753172207469611837324, 6605532282297186443646374610545079650832667420800652400938464833443600603, 2295548010993648132494168910744437729740138038458502495045159237302797445]]]
 hmul := by decide  
 g := ![![![![440980710441418165827521711529446237535763386905177618904462417534620284, 108287414463888302354858600172870158210371597062305777064564997269567223, 37631934606453248073674900176138323438362918663254139263035397332832745]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0)
instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0]] 
 ![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [16, 29, 16, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [60, 32, 51], [58, 34, 16], [0, 1]]
 g := ![![[13, 24, 14], [24, 28, 55], [45, 22], [18, 6], [51, 1], []], ![[23, 6, 36, 38], [54, 36, 16, 45], [15, 36], [45, 62], [16, 17], [39, 55]], ![[44, 23, 49, 36], [53, 51, 40, 15], [47, 26], [23, 59], [24, 19], [7, 55]]]
 h' := ![![[60, 32, 51], [18, 16, 58], [50, 20, 16], [57, 20, 25], [55, 46, 26], [0, 0, 1], [0, 1]], ![[58, 34, 16], [56, 64, 41], [23, 22, 23], [14, 1, 61], [59, 49, 14], [28, 20, 34], [60, 32, 51]], ![[0, 1], [19, 54, 35], [44, 25, 28], [40, 46, 48], [41, 39, 27], [36, 47, 32], [58, 34, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 27], []]
 b := ![[], [42, 22, 31], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [16, 29, 16, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6666098, 1703006, 568093]
  a := ![2, 19, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![99494, 25418, 8479]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def PBC67 : ContainsPrimesAboveP 67 ![I67N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![67, 0, 0]]) timesTableT_eq_Table B_one_repr 67 (by decide) 𝕀

instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1822976251186155520268522914811902, -447650838678225539949760549396743, -155567174367070428485213556120246]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-1822976251186155520268522914811902, -447650838678225539949760549396743, -155567174367070428485213556120246]] 
 ![![71, 0, 0], ![0, 71, 0], ![38, 22, 1]] where
  M :=![![![-1822976251186155520268522914811902, -447650838678225539949760549396743, -155567174367070428485213556120246], ![-17560040019055972673323251722623803, -4312051041059282376031939812735838, -1498519690401747048334495204310475], ![-55775413578021767390852629790692062, -13696234742268566635575138147398220, -4759701879737507915981700362132581]]]
  hmulB := by decide  
  f := ![![![-35835251202025118, -11899265096208147, 4917549966701313]], ![![529031231240936283, 42845548265195890, -30780245321923128]], ![![129219232107636658, 7134913313246828, -6469749509558749]]]
  g := ![![![57585582743134095241825242503626, 41898971794328505446830108242939, -155567174367070428485213556120246], ![554700115721273453005458676636257, 403596931658861305455309220874572, -1498519690401747048334495204310475], ![1761876871154979343893689915075296, 1281932487492346584732708025627022, -4759701879737507915981700362132581]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [25, 53, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 70], [0, 1]]
 g := ![![[22, 54], [24, 64], [27, 18], [24], [40], [1]], ![[0, 17], [40, 7], [67, 53], [24], [40], [1]]]
 h' := ![![[18, 70], [39, 57], [35, 63], [13, 35], [51, 33], [46, 18], [0, 1]], ![[0, 1], [0, 14], [33, 8], [4, 36], [6, 38], [15, 53], [18, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [21, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [25, 53, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2318, 717, 152]
  a := ![-2, 3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-114, -37, 152]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-35835251202025118, -11899265096208147, 4917549966701313]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-35835251202025118, -11899265096208147, 4917549966701313]] 
 ![![71, 0, 0], ![4, 1, 0], ![66, 0, 1]] where
  M :=![![![-35835251202025118, -11899265096208147, 4917549966701313], ![529031231240936283, 42845548265195890, -30780245321923128], ![-1102382061981441024, 16148857062124794, 30946283168987743]]]
  hmulB := by decide  
  f := ![![![-1822976251186155520268522914811902, -447650838678225539949760549396743, -155567174367070428485213556120246]], ![![-350027394701416827526723146223541, -85952878813692739941281436765110, -29870258984084912144723231391429]], ![![-2480166847271944108853171016454614, -609030846408893693975483583205398, -211649794196678256281771761493927]]]
  g := ![![![-4405584346753228, -11899265096208147, 4917549966701313], ![33649932808832101, 42845548265195890, -30780245321923128], ![-45203270132156778, 16148857062124794, 30946283168987743]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-1822976251186155520268522914811902, -447650838678225539949760549396743, -155567174367070428485213556120246]] ![![-35835251202025118, -11899265096208147, 4917549966701313]]
  ![![71, 0, 0]] where
 M := ![![![71, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0)

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![555656790221734421, -45018026995064286, -3987971805195669]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![555656790221734421, -45018026995064286, -3987971805195669]] 
 ![![73, 0, 0], ![27, 1, 0], ![25, 0, 1]] where
  M :=![![![555656790221734421, -45018026995064286, -3987971805195669], ![-483694925566587876, 491849241338603717, -139042052790388527], ![-5119477785275289558, -887783247739246674, 446831214343539431]]]
  hmulB := by decide  
  f := ![![![-96334388582693980476233730520155829, -23655914230663971688204145848316172, -8220879792832095973097651717548395]], ![![-48342207988697698651880226833189685, -11870933554738832214072713642540641, -4125375025908090442621187474469912]], ![![-73366948373141567513402749019941195, -18016019654194121508033854135862954, -6260909237253066946047145161478852]]]
  g := ![![![25627983756415916, -45018026995064286, -3987971805195669], ![-140925659204783220, 491849241338603717, -139042052790388527], ![105203966371176505, -887783247739246674, 446831214343539431]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N0)

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := prime_ideal_of_norm_prime hp73.out _ NI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12824129788403162263857579871, 743151208336606752869253206, 185176916229217289908713781]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-12824129788403162263857579871, 743151208336606752869253206, 185176916229217289908713781]] 
 ![![73, 0, 0], ![59, 1, 0], ![8, 0, 1]] where
  M :=![![![-12824129788403162263857579871, 743151208336606752869253206, 185176916229217289908713781], ![21112611993550508642827769116, -9861299128735685625318159375, 2414630541239037548516473399], ![89524063398653868991783831462, 19667849815012834222074030098, -9118147920399078872448906169]]]
  hmulB := by decide  
  f := ![![![-42426193299281995827485120298586823765738954472820321273, -10418194422439951844406517880776496906657979720857808352, -3620520567081407021312678183752533511351763402511314069]], ![![-39887957006288116137129085146714764182656852984842483713, -9794904017760844753266746934307406540276547567720712865, -3403915305372661326191510200924404128781914291962359852]], ![![-22431134201096846087667539903996104895000869424416392874, -5508199040492848481656012504880031962144733920630994402, -1914203853858571454567067323142796232121085696629447497]]]
  g := ![![![-796595430275297246608400401, 743151208336606752869253206, 185176916229217289908713781], ![7994687893959502193814621713, -9861299128735685625318159375, 2414630541239037548516473399], ![-13670327292108366015493050616, 19667849815012834222074030098, -9118147920399078872448906169]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![555656790221734421, -45018026995064286, -3987971805195669]] ![![-12824129788403162263857579871, 743151208336606752869253206, 185176916229217289908713781]]
  ![![-8433282372993387360652631159049393180971168945, 778438414926455332767592567175949829368139414, 30555824828635249556652973663051217137009748]] where
 M := ![![![-8433282372993387360652631159049393180971168945, 778438414926455332767592567175949829368139414, 30555824828635249556652973663051217137009748]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![-8433282372993387360652631159049393180971168945, 778438414926455332767592567175949829368139414, 30555824828635249556652973663051217137009748]] ![![-12824129788403162263857579871, 743151208336606752869253206, 185176916229217289908713781]]
  ![![73, 0, 0]] where
 M := ![![![127319857507893439012409562460712027334718208035677341719562594715946935695, -13342650674919045937955803512908685781065658518515619275646622902808598616, 39379417016694994033477041511233321525777331635634953881525118363381729]]]
 hmul := by decide  
 g := ![![![![1744107637094430671402870718639890785407098740214758105747432804328040215, -182776036642726656684326075519297065494050116691994784597898943874090392, 539444068721849233335301938510045500353114131994999368240070114566873]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1, I73N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
    exact isPrimeI73N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0 ⊙ MulI73N1)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![472221673, -9395160, -12476277]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![472221673, -9395160, -12476277]] 
 ![![79, 0, 0], ![0, 79, 0], ![17, 54, 1]] where
  M :=![![![472221673, -9395160, -12476277], ![-1381785630, 272601241, -40661757], ![-1557471234, -674326194, 263206081]]]
  hmulB := by decide  
  f := ![![![561152107344097, 137796754793262, 47886991217163]], ![![5405365788681192, 1327343966818705, 461277255596949]], ![![4032889051544477, 990317984145678, 344154321196696]]]
  g := ![![![8662258, 8409162, -12476277], ![-8740959, 31244761, -40661757], ![-76354109, -188448792, 263206081]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [12, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [65, 78], [0, 1]]
 g := ![![[67, 1], [33, 13], [27, 72], [20, 22], [38], [1]], ![[53, 78], [9, 66], [46, 7], [28, 57], [38], [1]]]
 h' := ![![[65, 78], [78, 78], [71, 31], [76, 25], [4, 41], [67, 65], [0, 1]], ![[0, 1], [13, 1], [32, 48], [42, 54], [62, 38], [26, 14], [65, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [33, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [12, 14, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2877, 1722, 699]
  a := ![2, 1, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-114, -456, 699]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-561152107344097, -137796754793262, -47886991217163]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![-561152107344097, -137796754793262, -47886991217163]] 
 ![![79, 0, 0], ![74, 1, 0], ![71, 0, 1]] where
  M :=![![![-561152107344097, -137796754793262, -47886991217163], ![-5405365788681192, -1327343966818705, -461277255596949], ![-17168896658379666, -4216001707813038, -1465140721611967]]]
  hmulB := by decide  
  f := ![![![-472221673, 9395160, 12476277]], ![![-424843268, 5349881, 12201345]], ![![-404686931, 16979526, 7881134]]]
  g := ![![![165009925617416, -137796754793262, -47886991217163], ![1589478138016283, -1327343966818705, -461277255596949], ![5048610391825757, -4216001707813038, -1465140721611967]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![472221673, -9395160, -12476277]] ![![-561152107344097, -137796754793262, -47886991217163]]
  ![![79, 0, 0]] where
 M := ![![![-79, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0)


lemma PB157I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB157I1 : PrimesBelowBoundCertificateInterval O 31 79 157 where
  m := 11
  g := ![1, 3, 1, 3, 2, 2, 2, 1, 2, 3, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB157I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1, I73N1]
    · exact ![I79N0, I79N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
    · exact PBC67
    · exact PBC71
    · exact PBC73
    · exact PBC79
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![50653]
    · exact ![41, 41, 41]
    · exact ![79507]
    · exact ![47, 47, 47]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![300763]
    · exact ![5041, 71]
    · exact ![73, 73, 73]
    · exact ![6241, 79]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
      exact NI41N2
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
      exact NI47N2
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I41N0, I41N1, I41N2, I47N0, I47N1, I47N2, I53N1, I59N1, I61N1, I71N1, I73N0, I73N1, I79N1]
  Il := ![[], [I41N0, I41N1, I41N2], [], [I47N0, I47N1, I47N2], [I53N1], [I59N1], [I61N1], [], [I71N1], [I73N0, I73N1, I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
