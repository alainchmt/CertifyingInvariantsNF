
import IdealArithmetic.Examples.NF3_1_371640_1.RI3_1_371640_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![797601893706505435903950189027584023103904996535429628, -23235085754609428837311022441824640885291930347852225, 34633778490837019167329682257169517637588793761882252]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![797601893706505435903950189027584023103904996535429628, -23235085754609428837311022441824640885291930347852225, 34633778490837019167329682257169517637588793761882252]] 
 ![![83, 0, 0], ![0, 1, 0], ![14, 0, 1]] where
  M :=![![![797601893706505435903950189027584023103904996535429628, -23235085754609428837311022441824640885291930347852225, 34633778490837019167329682257169517637588793761882252], ![-2412965801622363751383059098186521357878918699917727613, 70292545398928033390026861627024152714540327535902336, -104776736036819553856536452393778327674162788325231098], ![1083714239705495302264515314628357456521311287573569745, -31569876515757281926413762579225305972701369123337055, 47057459644318604552715839185199511829248397188050111]]]
  hmulB := by decide  
  f := ![![![1964109293815062634948222906, 568049225082655288304399115, -180761617088416529525247622]], ![![157115672339558985849957651, 69398834369539876566005096, 38885948595271267473507796]], ![![-108270387481519157359634987, -15240003846413723798217825, 45752889620682332890715125]]]
  g := ![![![3767819214876953826040176354544708146718817877940700, -23235085754609428837311022441824640885291930347852225, 34633778490837019167329682257169517637588793761882252], ![-11398692736227590330018659815344876752296863414030027, 70292545398928033390026861627024152714540327535902336, -104776736036819553856536452393778327674162788325231098], ![5119395237169094440078235735368244468817273818564677, -31569876515757281926413762579225305972701369123337055, 47057459644318604552715839185199511829248397188050111]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N0 : Nat.card (O ⧸ I83N0) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N0)

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := prime_ideal_of_norm_prime hp83.out _ NI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1964109293815062634948222906, -568049225082655288304399115, 180761617088416529525247622]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-1964109293815062634948222906, -568049225082655288304399115, 180761617088416529525247622]] 
 ![![83, 0, 0], ![0, 83, 0], ![21, 69, 1]] where
  M :=![![![-1964109293815062634948222906, -568049225082655288304399115, 180761617088416529525247622], ![-13040600804183395825546485033, -5760103252671809754978422968, -3227533733407515200301147068], ![36483972274376966950124824605, 9217609470409513111513667085, -6328152477754465043282822083]]]
  hmulB := by decide  
  f := ![![![-797601893706505435903950189027584023103904996535429628, 23235085754609428837311022441824640885291930347852225, -34633778490837019167329682257169517637588793761882252]], ![![2412965801622363751383059098186521357878918699917727613, -70292545398928033390026861627024152714540327535902336, 104776736036819553856536452393778327674162788325231098]], ![![1791099834992783004688959138441715081348699687704886908, -52176854881487698992794074920567756298065671006614788, 77773831067333171193185253597408978642152040099438173]]]
  g := ![![![-69398834369539876566005096, -157115672339558985849957651, 180761617088416529525247622], ![659489248161137631093706065, 2613731618704177579106032828, -3227533733407515200301147068], ![2040664750689406419988723956, 5371808800427320495156968564, -6328152477754465043282822083]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P1 : CertificateIrreducibleZModOfList' 83 2 2 6 [22, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [82, 82], [0, 1]]
 g := ![![[34, 33], [29, 81], [48], [16], [43, 1], [1]], ![[1, 50], [31, 2], [48], [16], [42, 82], [1]]]
 h' := ![![[82, 82], [26, 38], [40, 74], [73, 52], [50, 4], [61, 82], [0, 1]], ![[0, 1], [71, 45], [49, 9], [21, 31], [46, 79], [62, 1], [82, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [21, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N1 : CertifiedPrimeIdeal' SI83N1 83 where
  n := 2
  hpos := by decide
  P := [22, 1, 1]
  hirr := P83P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1345, -791, -732]
  a := ![-1, -1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![169, 599, -732]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N1 B_one_repr
lemma NI83N1 : Nat.card (O ⧸ I83N1) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![797601893706505435903950189027584023103904996535429628, -23235085754609428837311022441824640885291930347852225, 34633778490837019167329682257169517637588793761882252]] ![![-1964109293815062634948222906, -568049225082655288304399115, 180761617088416529525247622]]
  ![![83, 0, 0]] where
 M := ![![![-83, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61773141362386326, 19245713988993805, -2612427468297536]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![61773141362386326, 19245713988993805, -2612427468297536]] 
 ![![89, 0, 0], ![0, 89, 0], ![53, 83, 1]] where
  M :=![![![61773141362386326, 19245713988993805, -2612427468297536], ![199503209301523789, 116634118196634582, 112861856465665294], ![-1288767853216109505, -364973581744406865, 135879832185628387]]]
  hmulB := by decide  
  f := ![![![-640896858474993930852163437426096, 18670082887247800986172405777055, -27829271729467585661730845084198]], ![![1938889832220511211645600716586717, -56482152156174631955815690657938, 84191225594019220255303589578132]], ![![1416736246425277165711238921019782, -41271201130657876807294636668316, 61518070262616701237627189445411]]]
  g := ![![![2249795473956806, 2652552739974037, -2612427468297536], ![-64968260487401537, -103942696274759380, 112861856465665294], ![-95397741112970944, -130820220821927674, 135879832185628387]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [45, 62, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 88], [0, 1]]
 g := ![![[35, 2], [32], [34], [26, 5], [76, 17], [1]], ![[0, 87], [32], [34], [72, 84], [1, 72], [1]]]
 h' := ![![[27, 88], [37, 25], [63, 11], [76, 52], [51, 19], [44, 27], [0, 1]], ![[0, 1], [0, 64], [4, 78], [56, 37], [30, 70], [61, 62], [27, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65]]
 b := ![[], [73, 77]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [45, 62, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1230, -1575, -2719]
  a := ![2, -2, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1633, 2518, -2719]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-640896858474993930852163437426096, 18670082887247800986172405777055, -27829271729467585661730845084198]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-640896858474993930852163437426096, 18670082887247800986172405777055, -27829271729467585661730845084198]] 
 ![![89, 0, 0], ![35, 1, 0], ![63, 0, 1]] where
  M :=![![![-640896858474993930852163437426096, 18670082887247800986172405777055, -27829271729467585661730845084198], ![1938889832220511211645600716586717, -56482152156174631955815690657938, 84191225594019220255303589578132], ![-870796643278084483119933322353825, 25367335309809964216342154944815, -37812069268926830969643284880883]]]
  hmulB := by decide  
  f := ![![![61773141362386326, 19245713988993805, -2612427468297536]], ![![26534417494213991, 8879034919229413, 240751630059006]], ![![29246517445103697, 9522543815305650, -322506722664229]]]
  g := ![![![5156116398065066644054444951477, 18670082887247800986172405777055, -27829271729467585661730845084198], ![-15598674772321208381853665773121, -56482152156174631955815690657938, 84191225594019220255303589578132], ![7005696458662439555006946090711, 25367335309809964216342154944815, -37812069268926830969643284880883]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![61773141362386326, 19245713988993805, -2612427468297536]] ![![-640896858474993930852163437426096, 18670082887247800986172405777055, -27829271729467585661730845084198]]
  ![![89, 0, 0]] where
 M := ![![![89, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0]] 
 ![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [65, 43, 82, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [61, 89, 82], [51, 7, 15], [0, 1]]
 g := ![![[11, 58, 49], [91, 81], [53, 95], [2, 61], [48, 31], [1]], ![[50, 43, 74, 58], [78, 61], [1, 79], [71, 33], [55, 94], [92, 26, 41, 20]], ![[80, 83, 49, 41], [18, 94], [84, 65], [9, 93], [50, 24], [17, 75, 60, 77]]]
 h' := ![![[61, 89, 82], [8, 83, 90], [43, 84, 88], [53, 11, 17], [38, 56, 62], [32, 54, 15], [0, 1]], ![[51, 7, 15], [69, 66, 64], [80, 31, 35], [40, 93, 51], [75, 1, 79], [35, 13, 71], [61, 89, 82]], ![[0, 1], [25, 45, 40], [15, 79, 71], [72, 90, 29], [50, 40, 53], [14, 30, 11], [51, 7, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50, 47], []]
 b := ![[], [66, 23, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [65, 43, 82, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-46139657484, -21512463575, -14023168750]
  a := ![-65, 1, -326]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-475666572, -221777975, -144568750]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 912673 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def PBC97 : ContainsPrimesAboveP 97 ![I97N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![97, 0, 0]]) timesTableT_eq_Table B_one_repr 97 (by decide) 𝕀

instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1450, 579, 222]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![1450, 579, 222]] 
 ![![101, 0, 0], ![0, 101, 0], ![22, 34, 1]] where
  M :=![![![1450, 579, 222], ![-14739, -3212, 3696], ![-43281, -15489, -2633]]]
  hmulB := by decide  
  f := ![![![650540, -18951, 28248]], ![![-1968063, 57332, -85458]], ![![-512063, 14917, -22235]]]
  g := ![![![-34, -69, 222], ![-951, -1276, 3696], ![145, 733, -2633]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [3, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [86, 100], [0, 1]]
 g := ![![[5, 16], [97], [88, 54], [47], [97], [86, 1]], ![[68, 85], [97], [86, 47], [47], [97], [71, 100]]]
 h' := ![![[86, 100], [18, 4], [39, 20], [47, 16], [17, 42], [45, 20], [0, 1]], ![[0, 1], [59, 97], [42, 81], [9, 85], [94, 59], [48, 81], [86, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [17, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [3, 15, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-763, -1978, -3712]
  a := ![-2, 1, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![801, 1230, -3712]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![650540, -18951, 28248]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![650540, -18951, 28248]] 
 ![![101, 0, 0], ![98, 1, 0], ![66, 0, 1]] where
  M :=![![![650540, -18951, 28248], ![-1968063, 57332, -85458], ![883899, -25749, 38381]]]
  hmulB := by decide  
  f := ![![![1450, 579, 222]], ![![1261, 530, 252]], ![![519, 225, 119]]]
  g := ![![![6370, -18951, 28248], ![-19271, 57332, -85458], ![8655, -25749, 38381]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![1450, 579, 222]] ![![650540, -18951, 28248]]
  ![![101, 0, 0]] where
 M := ![![![101, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0)
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19806, -577, 860]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![19806, -577, 860]] 
 ![![103, 0, 0], ![0, 103, 0], ![18, 4, 1]] where
  M :=![![![19806, -577, 860], ![-59917, 1746, -2602], ![26913, -783, 1169]]]
  hmulB := by decide  
  f := ![![![36, 11, -2]], ![![149, 78, 64]], ![![5, 3, 3]]]
  g := ![![![42, -39, 860], ![-127, 118, -2602], ![57, -53, 1169]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [27, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [74, 102], [0, 1]]
 g := ![![[85, 8], [51, 98], [101, 18], [91], [100], [74, 1]], ![[59, 95], [93, 5], [94, 85], [91], [100], [45, 102]]]
 h' := ![![[74, 102], [65, 27], [54, 43], [33, 11], [11, 83], [62, 93], [0, 1]], ![[0, 1], [3, 76], [43, 60], [23, 92], [76, 20], [43, 10], [74, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [92, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [27, 29, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1368, -819, -900]
  a := ![-1, -1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![144, 27, -900]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![36, 11, -2]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![36, 11, -2]] 
 ![![103, 0, 0], ![78, 1, 0], ![102, 0, 1]] where
  M :=![![![36, 11, -2], ![149, 78, 64], ![-729, -201, 89]]]
  hmulB := by decide  
  f := ![![![19806, -577, 860]], ![![14417, -420, 626]], ![![19875, -579, 863]]]
  g := ![![![-6, 11, -2], ![-121, 78, 64], ![57, -201, 89]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![19806, -577, 860]] ![![36, 11, -2]]
  ![![103, 0, 0]] where
 M := ![![![103, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0)
instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![982103263315267123077538871053059654909430718946924789192811, -28609828691566303117002106154254509636553002560582891756310, 42645268454321521843451234161620769723766460959917327553218]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![982103263315267123077538871053059654909430718946924789192811, -28609828691566303117002106154254509636553002560582891756310, 42645268454321521843451234161620769723766460959917327553218]] 
 ![![107, 0, 0], ![0, 107, 0], ![23, 54, 1]] where
  M :=![![![982103263315267123077538871053059654909430718946924789192811, -28609828691566303117002106154254509636553002560582891756310, 42645268454321521843451234161620769723766460959917327553218], ![-2971133352039751310315137263306087620576438808794878492928352, 86552625774515164365062953659023490710335038788660910575233, -129013703695076296858561402763906288095551554403580022984642], ![1334399152903252087421376812219249619065660262281459617887120, -38872624291930462194724283184966843488883860626519186415760, 57942797082948861248060847504768981073782036228078018818923]]]
  hmulB := by decide  
  f := ![![![-124449723954960398928021600223, -22702964156229390597053656650, 41043900470825266941633049918]], ![![-2854732096643172809569734100992, -986371633842291004702315648501, -95173884466551076640688889982]], ![![-1458570381775495064906896557931, -503973202456621981675174281132, -48639763068815863497560833795]]]
  g := ![![![11795223045533838113649395661513563203758101577815471671, -21789292759111481146386623840016598829158335461645968033926, 42645268454321521843451234161620769723766460959917327553218], ![-35683804233611986618925231179841068960308948715308077398, 65918622666435842941377371055233299512804850248429739735943, -129013703695076296858561402763906288095551554403580022984642], ![16026355097460548747451585136103311856761019024908271513, -29605454829637093173738411667686839453019755298530207501286, 57942797082948861248060847504768981073782036228078018818923]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [96, 61, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [46, 106], [0, 1]]
 g := ![![[82, 4], [85, 34], [99], [29, 61], [62], [46, 1]], ![[52, 103], [44, 73], [99], [53, 46], [62], [92, 106]]]
 h' := ![![[46, 106], [79, 105], [23, 26], [105, 62], [25, 75], [78, 94], [0, 1]], ![[0, 1], [94, 2], [42, 81], [68, 45], [51, 32], [15, 13], [46, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64]]
 b := ![[], [13, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [96, 61, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-30074, -9358, 758]
  a := ![2, 19, 11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-444, -470, 758]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![124449723954960398928021600223, 22702964156229390597053656650, -41043900470825266941633049918]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![124449723954960398928021600223, 22702964156229390597053656650, -41043900470825266941633049918]] 
 ![![107, 0, 0], ![103, 1, 0], ![51, 0, 1]] where
  M :=![![![124449723954960398928021600223, 22702964156229390597053656650, -41043900470825266941633049918], ![2854732096643172809569734100992, 986371633842291004702315648501, 95173884466551076640688889982], ![-950846019717448947072206560080, 138896259781561801586368959120, 1009074597998520395299369305151]]]
  hmulB := by decide  
  f := ![![![-982103263315267123077538871053059654909430718946924789192811, 28609828691566303117002106154254509636553002560582891756310, -42645268454321521843451234161620769723766460959917327553218]], ![![-917621521209651984735246415468776232103690890119050231718983, 26731399340717888380244429721768140204248824532255859255371, -39845317262617200495485193606383485920115831069793502009316]], ![![-480576313850297900601643544260984037564921746996024522118883, 13999755958521606739830202776186419018253149450619127719510, -20867770918255574535178259717265684457811883599849174990963]]]
  g := ![![![-1128193085276431949020742887, 22702964156229390597053656650, -41043900470825266941633049918], ![-968181442027167341901344963399, 986371633842291004702315648501, 95173884466551076640688889982], ![-623551077337783688511551812263, 138896259781561801586368959120, 1009074597998520395299369305151]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![982103263315267123077538871053059654909430718946924789192811, -28609828691566303117002106154254509636553002560582891756310, 42645268454321521843451234161620769723766460959917327553218]] ![![124449723954960398928021600223, 22702964156229390597053656650, -41043900470825266941633049918]]
  ![![107, 0, 0]] where
 M := ![![![-107, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![810471, -8009890, -18431080]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![810471, -8009890, -18431080]] 
 ![![109, 0, 0], ![0, 109, 0], ![66, 99, 1]] where
  M :=![![![810471, -8009890, -18431080], ![1263734630, 387863151, -66490420], ![829148610, 444673890, 379853261]]]
  hmulB := by decide  
  f := ![![![1622914095763479, -47277405538990, 70470804728320]], ![![-4909762931793070, 143027196468759, -213193628505620]], ![![-3456413954273934, 100689423213099, -150085746046399]]]
  g := ![![![11167539, 16666670, -18431080], ![51854150, 63948759, -66490420], ![-222396024, -340924761, 379853261]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [56, 67, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [42, 108], [0, 1]]
 g := ![![[81, 84], [102], [34, 94], [25, 1], [97], [42, 1]], ![[12, 25], [102], [58, 15], [67, 108], [97], [84, 108]]]
 h' := ![![[42, 108], [50, 56], [58, 50], [17, 58], [63, 108], [46, 73], [0, 1]], ![[0, 1], [4, 53], [87, 59], [55, 51], [21, 1], [60, 36], [42, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62]]
 b := ![[], [3, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [56, 67, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2674, -240, -3246]
  a := ![-2, 3, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1990, 2946, -3246]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1622914095763479, -47277405538990, 70470804728320]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![1622914095763479, -47277405538990, 70470804728320]] 
 ![![109, 0, 0], ![59, 1, 0], ![74, 0, 1]] where
  M :=![![![1622914095763479, -47277405538990, 70470804728320], ![-4909762931793070, 143027196468759, -213193628505620], ![2205078911265510, -64236554606010, 95749790929769]]]
  hmulB := by decide  
  f := ![![![810471, -8009890, -18431080]], ![![12032591, -777251, -10586460]], ![![8157096, -1358330, -9027951]]]
  g := ![![![-7362922269099, -47277405538990, 70470804728320], ![22274871430881, 143027196468759, -213193628505620], ![-10004118309934, -64236554606010, 95749790929769]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![810471, -8009890, -18431080]] ![![1622914095763479, -47277405538990, 70470804728320]]
  ![![109, 0, 0]] where
 M := ![![![109, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11492556227859637447832738393084905380319298565638139567036, -334791744604669773140136272015915352999117686789909728315, 499034229770326966851122718867558644512773895751619285254]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![11492556227859637447832738393084905380319298565638139567036, -334791744604669773140136272015915352999117686789909728315, 499034229770326966851122718867558644512773895751619285254]] 
 ![![113, 0, 0], ![0, 113, 0], ![47, 2, 1]] where
  M :=![![![11492556227859637447832738393084905380319298565638139567036, -334791744604669773140136272015915352999117686789909728315, 499034229770326966851122718867558644512773895751619285254], ![-34768153598757230485867603873877461824380516493651640410841, 1012837402682771143959161296866173845551046754854134576702, -1509716237857691671989694913227933473481932224987839084636], ![15615116931167309843902561986084779689247511952229481974925, -454886809856839266823979070679157254710137013686184984195, 678045658078101370819025024850258492551929068064224848387]]]
  hmulB := by decide  
  f := ![![![-1857657557878366383863317242, -2696570615227413780760624625, -4636887941554708298442742336]], ![![317248697352047458811788596559, 95516989214770507883434271814, -20816311632919190983006490086]], ![![7104461779272777636558632893, 1685632403158839663218879986, -1475627769197934317611931175]]]
  g := ![![![-105858872312794070744867516758321689484788270218477582654, -11795223045533838113649395661513563203758101577815471671, 499034229770326966851122718867558644512773895751619285254], ![320252297173046708828743867679959393179383168856431828027, 35683804233611986618925231179841068960308948715308077398, -1509716237857691671989694913227933473481932224987839084636], ![-143832115031004022872492160901569641245072161476009609728, -16026355097460548747451585136103311856761019024908271513, 678045658078101370819025024850258492551929068064224848387]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [100, 57, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [56, 112], [0, 1]]
 g := ![![[13, 26], [62], [44], [31], [26, 112], [56, 1]], ![[0, 87], [62], [44], [31], [83, 1], [112, 112]]]
 h' := ![![[56, 112], [17, 34], [51, 66], [65, 65], [112, 101], [50, 98], [0, 1]], ![[0, 1], [0, 79], [18, 47], [89, 48], [5, 12], [1, 15], [56, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94]]
 b := ![[], [40, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [100, 57, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3597, -2603, -2262]
  a := ![2, 1, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![909, 17, -2262]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1857657557878366383863317242, -2696570615227413780760624625, -4636887941554708298442742336]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![-1857657557878366383863317242, -2696570615227413780760624625, -4636887941554708298442742336]] 
 ![![113, 0, 0], ![100, 1, 0], ![85, 0, 1]] where
  M :=![![![-1857657557878366383863317242, -2696570615227413780760624625, -4636887941554708298442742336], ![317248697352047458811788596559, 95516989214770507883434271814, -20816311632919190983006490086], ![255616691574012175349124234165, 126181302043096313872614252165, 92820418599543094102673647189]]]
  hmulB := by decide  
  f := ![![![11492556227859637447832738393084905380319298565638139567036, -334791744604669773140136272015915352999117686789909728315, 499034229770326966851122718867558644512773895751619285254]], ![![9862720966258464728295630402076221913341144602390816958343, -287312717325523948407561645174560720835050636496786179246, 428262891497123938169226344898477265290225286284726455228]], ![![8783030055745455689466241817684086168286618495853728718345, -255860045143838672422438603469309400527744605228570901690, 381380134411999057992605806447723391824227523955326230929]]]
  g := ![![![5857830787584187761591435786, -2696570615227413780760624625, -4636887941554708298442742336], ![-66062510932096213238726432987, 95516989214770507883434271814, -20816311632919190983006490086], ![-179223443307051170005659831800, 126181302043096313872614252165, 92820418599543094102673647189]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![11492556227859637447832738393084905380319298565638139567036, -334791744604669773140136272015915352999117686789909728315, 499034229770326966851122718867558644512773895751619285254]] ![![-1857657557878366383863317242, -2696570615227413780760624625, -4636887941554708298442742336]]
  ![![113, 0, 0]] where
 M := ![![![113, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![360616812031358449383723514035479355495, -10505193904649504378940138723520797274, 15658842947233101653748094622274696272]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![360616812031358449383723514035479355495, -10505193904649504378940138723520797274, 15658842947233101653748094622274696272]] 
 ![![127, 0, 0], ![0, 127, 0], ![45, 94, 1]] where
  M :=![![![360616812031358449383723514035479355495, -10505193904649504378940138723520797274, 15658842947233101653748094622274696272], ![-1090965357263733518487558667660474840042, 31781110139463314655013526967710733783, -47372320480663924619892737718850087372], ![489975735212319277340648152588814567826, -14273572210856932848478506140183701326, 21275916234813810276073388244189936509]]]
  hmulB := by decide  
  f := ![![![2524005820654481325, 485572144548871022, -776480378713190024]], ![![54062718275758982678, 18830093773631471829, 2136952488580036108]], ![![40737153602815919537, 14120706707647473282, 1458642384272521149]]]
  g := ![![![-2708906461371111220747564913125054935, -11672727802713079211269771915097183046, 15658842947233101653748094622274696272], ![8195189483197977081949720706202984974, 35313222325369072668700243090863141313, -47372320480663924619892737718850087372], ![-3680633821687418780178380459840413977, -15859918884120906289758874024362501836, 21275916234813810276073388244189936509]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [2, 74, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [53, 126], [0, 1]]
 g := ![![[37, 64], [85, 64], [107, 76], [38, 50], [105, 42], [53, 1]], ![[0, 63], [48, 63], [71, 51], [21, 77], [45, 85], [106, 126]]]
 h' := ![![[53, 126], [84, 8], [40, 119], [51, 40], [44, 80], [21, 13], [0, 1]], ![[0, 1], [0, 119], [124, 8], [12, 87], [93, 47], [75, 114], [53, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72]]
 b := ![[], [62, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [2, 74, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9718, -9375, -14725]
  a := ![-5, 0, -25]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5141, 10825, -14725]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2524005820654481325, -485572144548871022, 776480378713190024]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![-2524005820654481325, -485572144548871022, 776480378713190024]] 
 ![![127, 0, 0], ![70, 1, 0], ![9, 0, 1]] where
  M :=![![![-2524005820654481325, -485572144548871022, 776480378713190024], ![-54062718275758982678, -18830093773631471829, -2136952488580036108], ![21857272293174250158, -1450190645171558898, -19315665918180342851]]]
  hmulB := by decide  
  f := ![![![-360616812031358449383723514035479355495, 10505193904649504378940138723520797274, -15658842947233101653748094622274696272]], ![![-190174893582136676680103049723016378304, 5540019395165370014730678611643662011, -8257847919887033001121841620790383084]], ![![-29413598767673585210977636054394714703, 856852892540964348495588619306069896, -1277208683148911221730757794052458291]]]
  g := ![![![192737959758643937, -485572144548871022, 776480378713190024], ![10104538726580034412, -18830093773631471829, -2136952488580036108], ![2340248903297688651, -1450190645171558898, -19315665918180342851]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![360616812031358449383723514035479355495, -10505193904649504378940138723520797274, 15658842947233101653748094622274696272]] ![![-2524005820654481325, -485572144548871022, 776480378713190024]]
  ![![127, 0, 0]] where
 M := ![![![-127, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0)
instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-268363338387001209571048423119488434890, 7817741193966756107670596089334888099, -11652976867400749191053695558388076456]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![-268363338387001209571048423119488434890, 7817741193966756107670596089334888099, -11652976867400749191053695558388076456]] 
 ![![131, 0, 0], ![18, 1, 0], ![99, 0, 1]] where
  M :=![![![-268363338387001209571048423119488434890, 7817741193966756107670596089334888099, -11652976867400749191053695558388076456], ![811873145044618450290375589618112163563, -23650824171585476558920816393338829314, 35253470296399787454969880977621252138], ![-364629489372694933563465696788286131991, 10622087937709359604722915499788496761, -15833082977618720451250220304003941215]]]
  hmulB := by decide  
  f := ![![![12422093307402548508, 404486113577258731, -8241908853128474478]], ![![6051098293989983747, 1471625414255657784, -1176865278839522616]], ![![10118368919030141733, 1184569081343154948, -4809483291015581695]]]
  g := ![![![5683679618276880537444249675976359912, 7817741193966756107670596089334888099, -11652976867400749191053695558388076456], ![-17194699077942152135046320092261777637, -23650824171585476558920816393338829314, 35253470296399787454969880977621252138], ![7722504904830457391032775834442069516, 10622087937709359604722915499788496761, -15833082977618720451250220304003941215]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N0 : Nat.card (O ⧸ I131N0) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N0)

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := prime_ideal_of_norm_prime hp131.out _ NI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17830111120255647, -7391390768694434, -3334682358474554]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![-17830111120255647, -7391390768694434, -3334682358474554]] 
 ![![131, 0, 0], ![49, 1, 0], ![124, 0, 1]] where
  M :=![![![-17830111120255647, -7391390768694434, -3334682358474554], ![222701691966049792, 52198218407709987, -47683026970641158], ![560026198417034256, 205239441519701424, 44806827639015553]]]
  hmulB := by decide  
  f := ![![![12125274400681201951884119812036803, -353223572713416066373931351032894, 526508363442196995600921317085370]], ![![4255390419718731960912094416487633, -123964551866887955786701252269983, 184779211723888193754217387389856]], ![![11603120814885967905949758016469868, -338012621687899311225410297043272, 503835208110794476583244916952649]]]
  g := ![![![5785104190813865, -7391390768694434, -3334682358474554], ![27310567437769191, 52198218407709987, -47683026970641158], ![-114906511933482932, 205239441519701424, 44806827639015553]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1

def I131N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![412, 129, -16]] i)))

def SI131N2: IdealEqSpanCertificate' Table ![![412, 129, -16]] 
 ![![131, 0, 0], ![63, 1, 0], ![81, 0, 1]] where
  M :=![![![412, 129, -16], ![1233, 748, 758], ![-8661, -2469, 877]]]
  hmulB := by decide  
  f := ![![![-2527498, 73629, -109750]], ![![-1157145, 33709, -50246]], ![![-1589019, 46290, -68999]]]
  g := ![![![-49, 129, -16], ![-819, 748, 758], ![579, -2469, 877]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N2 : Nat.card (O ⧸ I131N2) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N2)

lemma isPrimeI131N2 : Ideal.IsPrime I131N2 := prime_ideal_of_norm_prime hp131.out _ NI131N2
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![-268363338387001209571048423119488434890, 7817741193966756107670596089334888099, -11652976867400749191053695558388076456]] ![![-17830111120255647, -7391390768694434, -3334682358474554]]
  ![![-2527498, 73629, -109750]] where
 M := ![![![-2527498, 73629, -109750]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI131N1 : IdealMulLeCertificate' Table 
  ![![-2527498, 73629, -109750]] ![![412, 129, -16]]
  ![![131, 0, 0]] where
 M := ![![![131, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1, I131N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
    exact isPrimeI131N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0 ⊙ MulI131N1)
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-133148946111291093428037, -49840750229027281551164, -12977751653679123000674]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-133148946111291093428037, -49840750229027281551164, -12977751653679123000674]] 
 ![![137, 0, 0], ![0, 137, 0], ![7, 75, 1]] where
  M :=![![![-133148946111291093428037, -49840750229027281551164, -12977751653679123000674], ![845624113874832205495342, 139383838615970489586117, -312022253027842812307658], ![3633678040608069272040426, 1241322029614759757584554, 89543088386943208034953]]]
  hmulB := by decide  
  f := ![![![-2918255151783892199386085847570764886063038409, 85012221310597984875330300434046717347329592, -126717605993822044278182355811547158146044210]], ![![8828527034884319040069912851430800629424380082, -257185425913629269544256375528274564996109999, 383355721869765864973799446792733145937933342]], ![![4655085126812501841732232171763056035617606997, -135608131036228002481030051339591525878687599, 202134910172793096922764641924671007231196429]]]
  g := ![![![-308793317777644032287, 6740807472970123675178, -12977751653679123000674], ![22115181642844758333204, 171832502304410083304091, -312022253027842812307658], ![21948003079558151940115, -39959194156248035365233, 89543088386943208034953]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [87, 87, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [50, 136], [0, 1]]
 g := ![![[1, 63], [93], [1], [95, 11], [32], [34], [1]], ![[0, 74], [93], [1], [97, 126], [32], [34], [1]]]
 h' := ![![[50, 136], [118, 36], [20, 97], [92, 1], [110, 82], [90, 124], [50, 50], [0, 1]], ![[0, 1], [0, 101], [75, 40], [5, 136], [100, 55], [125, 13], [84, 87], [50, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [96]]
 b := ![[], [33, 48]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [87, 87, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![23651, 1030, -7914]
  a := ![4, -10, 22]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![577, 4340, -7914]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2918255151783892199386085847570764886063038409, -85012221310597984875330300434046717347329592, 126717605993822044278182355811547158146044210]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![2918255151783892199386085847570764886063038409, -85012221310597984875330300434046717347329592, 126717605993822044278182355811547158146044210]] 
 ![![137, 0, 0], ![97, 1, 0], ![76, 0, 1]] where
  M :=![![![2918255151783892199386085847570764886063038409, -85012221310597984875330300434046717347329592, 126717605993822044278182355811547158146044210], ![-8828527034884319040069912851430800629424380082, 257185425913629269544256375528274564996109999, -383355721869765864973799446792733145937933342], ![3965079180523930292225055392776016124775078698, -115507442384772981790799028058226307896741718, 172173204603031284668926075094227847648780407]]]
  hmulB := by decide  
  f := ![![![133148946111291093428037, 49840750229027281551164, 12977751653679123000674]], ![![88100902619856962460031, 34271306084669166575743, 11466161776895749951628]], ![![47340451560949298018178, 18588138597016887885430, 6545737498486643357783]]]
  g := ![![![11196369075776798300374203999968704012077729, -85012221310597984875330300434046717347329592, 126717605993822044278182355811547158146044210], ![-33872105740176295239810389207486966005577489, 257185425913629269544256375528274564996109999, -383355721869765864973799446792733145937933342], ![15212682788441838621125397133304026054392076, -115507442384772981790799028058226307896741718, 172173204603031284668926075094227847648780407]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-133148946111291093428037, -49840750229027281551164, -12977751653679123000674]] ![![2918255151783892199386085847570764886063038409, -85012221310597984875330300434046717347329592, 126717605993822044278182355811547158146044210]]
  ![![137, 0, 0]] where
 M := ![![![-137, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0)


lemma PB173I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB173I2 : PrimesBelowBoundCertificateInterval O 79 137 173 where
  m := 11
  g := ![2, 2, 1, 2, 2, 2, 2, 2, 2, 3, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB173I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1, I131N2]
    · exact ![I137N0, I137N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC83
    · exact PBC89
    · exact PBC97
    · exact PBC101
    · exact PBC103
    · exact PBC107
    · exact PBC109
    · exact PBC113
    · exact PBC127
    · exact PBC131
    · exact PBC137
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![83, 6889]
    · exact ![7921, 89]
    · exact ![912673]
    · exact ![10201, 101]
    · exact ![10609, 103]
    · exact ![11449, 107]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![16129, 127]
    · exact ![131, 131, 131]
    · exact ![18769, 137]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
      exact NI131N2
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N0, I89N1, I101N1, I103N1, I107N1, I109N1, I113N1, I127N1, I131N0, I131N1, I131N2, I137N1]
  Il := ![[I83N0], [I89N1], [], [I101N1], [I103N1], [I107N1], [I109N1], [I113N1], [I127N1], [I131N0, I131N1, I131N2], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
