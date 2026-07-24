
import IdealArithmetic.Examples.NF3_1_837620_1.RI3_1_837620_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0]] 
 ![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 3 2 7 [114, 131, 125, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [91, 56, 32], [178, 140, 165], [0, 1]]
 g := ![![[153, 19, 88], [2, 29], [182, 96, 90], [13, 135], [173, 19], [178, 62], [1]], ![[44, 58, 78, 94], [147, 54], [143, 183, 181, 20], [187, 142], [71, 138], [196, 90], [118, 152, 75, 66]], ![[49, 187, 74, 72], [150, 157], [12, 194, 20, 141], [69, 101], [112, 136], [103, 136], [194, 32, 5, 131]]]
 h' := ![![[91, 56, 32], [195, 59, 65], [134, 126, 134], [35, 34, 22], [27, 153, 23], [190, 73, 120], [83, 66, 72], [0, 1]], ![[178, 140, 165], [99, 1, 153], [167, 174, 137], [67, 189, 31], [75, 86, 39], [17, 142, 27], [187, 107, 175], [91, 56, 32]], ![[0, 1], [10, 137, 176], [103, 94, 123], [21, 171, 144], [91, 155, 135], [137, 179, 50], [181, 24, 147], [178, 140, 165]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [153, 86], []]
 b := ![[], [14, 116, 182], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 3
  hpos := by decide
  P := [114, 131, 125, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4012693, -341795, 35460]
  a := ![-1, -5, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-20369, -1735, 180]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 7645373 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def PBC197 : ContainsPrimesAboveP 197 ![I197N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![197, 0, 0]]) timesTableT_eq_Table B_one_repr 197 (by decide) 𝕀

instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8407041, 1289806, 345874]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![8407041, 1289806, 345874]] 
 ![![199, 0, 0], ![0, 199, 0], ![57, 57, 1]] where
  M :=![![![8407041, 1289806, 345874], ![-59238144, 11836895, 11860438], ![-183519422, -11983014, 3500001]]]
  hmulB := by decide  
  f := ![![![-922376577573, 43512237558, -56299446602]], ![![9895915392908, -466830394331, 604020715386]], ![![2497530343799, -117818617981, 152442700353]]]
  g := ![![![-56823, -92588, 345874], ![-3694890, -3337729, 11860438], ![-1924721, -1062729, 3500001]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [54, 108, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [91, 198], [0, 1]]
 g := ![![[2, 184], [7, 128], [196, 175], [111], [102], [47], [91, 1]], ![[30, 15], [113, 71], [2, 24], [111], [102], [47], [182, 198]]]
 h' := ![![[91, 198], [20, 69], [162, 160], [172, 37], [185, 132], [188, 36], [61, 68], [0, 1]], ![[0, 1], [130, 130], [195, 39], [156, 162], [58, 67], [81, 163], [80, 131], [91, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [144]]
 b := ![[], [107, 72]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [54, 108, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10012, -7500, 633]
  a := ![2, 6, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-131, -219, 633]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-922376577573, 43512237558, -56299446602]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![-922376577573, 43512237558, -56299446602]] 
 ![![199, 0, 0], ![30, 1, 0], ![117, 0, 1]] where
  M :=![![![-922376577573, 43512237558, -56299446602], ![9895915392908, -466830394331, 604020715386], ![-14483174058094, 683229957842, -884014950441]]]
  hmulB := by decide  
  f := ![![![8407041, 1289806, 345874]], ![![969714, 253925, 111742]], ![![4020625, 698112, 220941]]]
  g := ![![![21905987679, 43512237558, -56299446602], ![-235023097876, -466830394331, 604020715386], ![343968223157, 683229957842, -884014950441]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![8407041, 1289806, 345874]] ![![-922376577573, 43512237558, -56299446602]]
  ![![199, 0, 0]] where
 M := ![![![199, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC199 : ContainsPrimesAboveP 199 ![I199N0, I199N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
    exact isPrimeI199N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 199 (by decide) (𝕀 ⊙ MulI199N0)
instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1050824514535817, 64378205587088, -22935210360512]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![1050824514535817, 64378205587088, -22935210360512]] 
 ![![211, 0, 0], ![0, 211, 0], ![201, 142, 1]] where
  M :=![![![1050824514535817, 64378205587088, -22935210360512], ![4078040018676688, 1423013388686729, 712587686952416], ![-14064281641722864, 45072337832752, 926495528856089]]]
  hmulB := by decide  
  f := ![![![6096196915444681051915425659, -287582289961371330995211696, 372095867416138858109573696]], ![![-65404359087785671500170608496, 3085388418518501437386710395, -3992110501862129884280838048]], ![![-37755264520820737146804245551, 1781068685869858774900939358, -2304482302041223481598494551]]]
  g := ![![![26828444535539, 15740180458672, -22935210360512], ![-659488554780848, -472817242457613, 712587686952416], ![-949241151382923, -623304705022426, 926495528856089]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [26, 103, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [108, 210], [0, 1]]
 g := ![![[77, 16], [153, 123], [119], [185], [40, 14], [34], [108, 1]], ![[117, 195], [144, 88], [119], [185], [75, 197], [34], [5, 210]]]
 h' := ![![[108, 210], [31, 4], [155, 40], [57, 69], [15, 117], [176, 15], [146, 33], [0, 1]], ![[0, 1], [41, 207], [44, 171], [124, 142], [202, 94], [108, 196], [123, 178], [108, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [122]]
 b := ![[], [82, 61]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [26, 103, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11161951, -6736759, -1254200]
  a := ![-65, -259, -586]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1141859, 812131, -1254200]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6096196915444681051915425659, -287582289961371330995211696, 372095867416138858109573696]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![6096196915444681051915425659, -287582289961371330995211696, 372095867416138858109573696]] 
 ![![211, 0, 0], ![60, 1, 0], ![17, 0, 1]] where
  M :=![![![6096196915444681051915425659, -287582289961371330995211696, 372095867416138858109573696], ![-65404359087785671500170608496, 3085388418518501437386710395, -3992110501862129884280838048], ![95722596568008923613530037712, -4515622428851365074777120656, 5842656183080378470572339659]]]
  hmulB := by decide  
  f := ![![![1050824514535817, 64378205587088, -22935210360512]], ![![318139862041828, 25050738028019, -3144667936864]], ![![18008223248275, 5400482619968, 2543113520035]]]
  g := ![![![80689595104514693477561017, -287582289961371330995211696, 372095867416138858109573696], ![-865695666669381752182933580, 3085388418518501437386710395, -3992110501862129884280838048], ![1266989512733290967300604279, -4515622428851365074777120656, 5842656183080378470572339659]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![1050824514535817, 64378205587088, -22935210360512]] ![![6096196915444681051915425659, -287582289961371330995211696, 372095867416138858109573696]]
  ![![211, 0, 0]] where
 M := ![![![211, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC211 : ContainsPrimesAboveP 211 ![I211N0, I211N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
    exact isPrimeI211N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 211 (by decide) (𝕀 ⊙ MulI211N0)
instance hp223 : Fact (Nat.Prime 223) := {out := by norm_num}

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1102715506108764581190679, -66464344455159584948120, -115640706741257326834084]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![1102715506108764581190679, -66464344455159584948120, -115640706741257326834084]] 
 ![![223, 0, 0], ![0, 223, 0], ![93, 45, 1]] where
  M :=![![![1102715506108764581190679, -66464344455159584948120, -115640706741257326834084], ![20170659335264872611016580, 1415061661994412875568619, -317721324327823868978948], ![-2476905942780466507837248, 2182573030135915154085944, 1649030659698015316537291]]]
  hmulB := by decide  
  f := ![![![-13573677397170363364170098161464930018247809767, 640325318098819809698815747799307197507103912, -828501660163076494937519827145578302477677972]], ![![145628115846637206423764785498275510131100749012, -6869867823959701650687236034539809715831004259, 8888758161477427581800716959429806882504073036]], ![![22770309784549962767362897056634619514513307175, -1074167701896328282997441787056606058260660089, 1389839975337849927548829297427696909770955819]]]
  g := ![![![53171754408276663572917, 23037522237226099204420, -115640706741257326834084], ![222954002232073957067528, 70459736577338506635073, -317721324327823868978948], ![-698819539438098165676257, -322976711463115578879337, 1649030659698015316537291]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 2 2 7 [33, 112, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [111, 222], [0, 1]]
 g := ![![[98, 196], [34, 68], [103, 36], [105, 8], [194, 178], [83], [111, 1]], ![[0, 27], [0, 155], [85, 187], [101, 215], [105, 45], [83], [222, 222]]]
 h' := ![![[111, 222], [216, 209], [169, 115], [103, 6], [65, 30], [42, 160], [128, 23], [0, 1]], ![[0, 1], [0, 14], [0, 108], [100, 217], [50, 193], [185, 63], [5, 200], [111, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47]]
 b := ![[], [201, 135]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 2
  hpos := by decide
  P := [33, 112, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2214, -9086, -3983]
  a := ![-2, -7, -21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1671, 763, -3983]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 49729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13573677397170363364170098161464930018247809767, -640325318098819809698815747799307197507103912, 828501660163076494937519827145578302477677972]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![13573677397170363364170098161464930018247809767, -640325318098819809698815747799307197507103912, 828501660163076494937519827145578302477677972]] 
 ![![223, 0, 0], ![222, 1, 0], ![45, 0, 1]] where
  M :=![![![13573677397170363364170098161464930018247809767, -640325318098819809698815747799307197507103912, 828501660163076494937519827145578302477677972], ![-145628115846637206423764785498275510131100749012, 6869867823959701650687236034539809715831004259, -8888758161477427581800716959429806882504073036], ![213134133207188799079670174776639312466019897184, -10054399972115124870506238495332716852107327992, 13009148370977593308453985923426116703336087587]]]
  hmulB := by decide  
  f := ![![![-1102715506108764581190679, 66464344455159584948120, 115640706741257326834084]], ![![-1188221980678971343656266, 59820730076461950596027, 116546897851510988458052]], ![![-211413864717999729353109, 3624764441014646495872, 15940812303401634040343]]]
  g := ![![![531135978958609501547617945970224682750355917, -640325318098819809698815747799307197507103912, 828501660163076494937519827145578302477677972], ![-5698406526902272339440802340770277835573544430, 6869867823959701650687236034539809715831004259, -8888758161477427581800716959429806882504073036], ![8339906952119976777809980960476803596339563991, -10054399972115124870506238495332716852107327992, 13009148370977593308453985923426116703336087587]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![1102715506108764581190679, -66464344455159584948120, -115640706741257326834084]] ![![13573677397170363364170098161464930018247809767, -640325318098819809698815747799307197507103912, 828501660163076494937519827145578302477677972]]
  ![![223, 0, 0]] where
 M := ![![![-223, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC223 : ContainsPrimesAboveP 223 ![I223N0, I223N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI223N0
    exact isPrimeI223N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 223 (by decide) (𝕀 ⊙ MulI223N0)
instance hp227 : Fact (Nat.Prime 227) := {out := by norm_num}

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![227, 0, 0]] 
 ![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 3 2 7 [188, 190, 155, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [52, 136, 138], [20, 90, 89], [0, 1]]
 g := ![![[77, 159, 173], [170, 205, 155], [92, 92], [81, 171], [58, 205], [161, 167, 190], [1]], ![[34, 48, 146, 107], [49, 119, 203, 174], [223, 210], [103, 77], [10, 102], [204, 117, 73, 55], [212, 106, 82, 93]], ![[45, 164, 214, 70], [49, 214, 188, 121], [202, 65], [199, 23], [174, 29], [167, 12, 40, 85], [45, 145, 217, 134]]]
 h' := ![![[52, 136, 138], [47, 209, 20], [15, 122, 90], [115, 207, 186], [19, 223, 25], [150, 144, 146], [39, 37, 72], [0, 1]], ![[20, 90, 89], [6, 191, 224], [58, 206, 193], [21, 8, 133], [192, 201, 109], [211, 9, 97], [191, 186, 9], [52, 136, 138]], ![[0, 1], [213, 54, 210], [55, 126, 171], [203, 12, 135], [29, 30, 93], [196, 74, 211], [221, 4, 146], [20, 90, 89]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 110], []]
 b := ![[], [141, 66, 65], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 3
  hpos := by decide
  P := [188, 190, 155, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4170898, -401790, 24970]
  a := ![-1, -5, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-18374, -1770, 110]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 11697083 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def PBC227 : ContainsPrimesAboveP 227 ![I227N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI227N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![227, 0, 0]]) timesTableT_eq_Table B_one_repr 227 (by decide) 𝕀

instance hp229 : Fact (Nat.Prime 229) := {out := by norm_num}

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![229, 0, 0]] 
 ![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 3 2 7 [18, 210, 119, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [29, 77, 26], [81, 151, 203], [0, 1]]
 g := ![![[62, 33, 97], [149, 172], [39, 39, 180], [133, 46], [102, 17], [12, 110, 192], [1]], ![[122, 211, 72, 193], [12, 68], [66, 212, 129, 118], [44, 14], [18, 184], [222, 49, 161, 78], [50, 50, 120, 172]], ![[175, 25, 150, 55], [133, 154], [0, 175, 144, 218], [158, 121], [10, 129], [14, 196, 83, 71], [125, 226, 142, 57]]]
 h' := ![![[29, 77, 26], [62, 174, 28], [214, 222, 114], [99, 224, 167], [165, 228, 59], [13, 175, 186], [211, 19, 110], [0, 1]], ![[81, 151, 203], [205, 147, 50], [119, 127, 86], [64, 217, 126], [216, 111, 181], [178, 219, 118], [131, 129, 158], [29, 77, 26]], ![[0, 1], [80, 137, 151], [111, 109, 29], [209, 17, 165], [63, 119, 218], [48, 64, 154], [201, 81, 190], [81, 151, 203]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [226, 36], []]
 b := ![[], [223, 23, 210], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 3
  hpos := by decide
  P := [18, 210, 119, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1973064, -6096438, -4290086]
  a := ![2, 27, 19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8616, -26622, -18734]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 12008989 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def PBC229 : ContainsPrimesAboveP 229 ![I229N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI229N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![229, 0, 0]]) timesTableT_eq_Table B_one_repr 229 (by decide) 𝕀

instance hp233 : Fact (Nat.Prime 233) := {out := by norm_num}

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![233, 0, 0]] 
 ![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 3 2 7 [30, 92, 92, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [110, 63, 84], [31, 169, 149], [0, 1]]
 g := ![![[74, 107, 14], [163, 133], [108, 202], [150, 208, 203], [202, 218], [182, 150, 76], [1]], ![[80, 121, 90, 136], [1, 33], [162, 121], [86, 80, 123, 211], [32, 177], [49, 216, 179, 153], [53, 16, 114, 185]], ![[116, 73, 34, 61], [130, 157], [86, 38], [37, 128, 229, 97], [174, 58], [151, 150, 79, 228], [138, 134, 154, 48]]]
 h' := ![![[110, 63, 84], [67, 55, 108], [225, 106, 42], [160, 11, 193], [180, 107, 73], [132, 160, 190], [203, 141, 141], [0, 1]], ![[31, 169, 149], [201, 177, 38], [109, 118, 158], [92, 228, 222], [81, 221, 122], [153, 231, 115], [145, 8, 24], [110, 63, 84]], ![[0, 1], [218, 1, 87], [33, 9, 33], [41, 227, 51], [26, 138, 38], [54, 75, 161], [21, 84, 68], [31, 169, 149]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [230, 222], []]
 b := ![[], [219, 60, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 3
  hpos := by decide
  P := [30, 92, 92, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-19043323, -1581138, -468563]
  a := ![-2, -5, -19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-81731, -6786, -2011]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 12649337 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def PBC233 : ContainsPrimesAboveP 233 ![I233N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI233N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![233, 0, 0]]) timesTableT_eq_Table B_one_repr 233 (by decide) 𝕀

instance hp239 : Fact (Nat.Prime 239) := {out := by norm_num}

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![38124440343, 378690009638, 256319449716]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![38124440343, 378690009638, 256319449716]] 
 ![![239, 0, 0], ![153, 1, 0], ![227, 0, 1]] where
  M :=![![![38124440343, 378690009638, 256319449716], ![-44477213690662, 271287230315, 3017941747232], ![-34999778821298, -5994561243646, -1866903937719]]]
  hmulB := by decide  
  f := ![![![-17584769435010285329336387, 829544769092175059768814, -1073328195756890086481476]], ![![-10467814830669563661901423, 493809206239521545969769, -638927956789170553868340]], ![![-17857150779166552283554989, 842394099876874914863516, -1089953638459540543433027]]]
  g := ![![![-485715322677, 378690009638, 256319449716], ![-3226179650839, 271287230315, 3017941747232], ![5464248055727, -5994561243646, -1866903937719]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N0 : Nat.card (O ⧸ I239N0) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N0)

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := prime_ideal_of_norm_prime hp239.out _ NI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16376488308475979292971910421248025082253664084475098, 772545256427893840672617234892144606455380263618547, -999577885506694260486809487166863304224174472319960]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![-16376488308475979292971910421248025082253664084475098, 772545256427893840672617234892144606455380263618547, -999577885506694260486809487166863304224174472319960]] 
 ![![239, 0, 0], ![158, 1, 0], ![189, 0, 1]] where
  M :=![![![-16376488308475979292971910421248025082253664084475098, 772545256427893840672617234892144606455380263618547, -999577885506694260486809487166863304224174472319960], ![175698675220099389425864277489093222845685912919611547, -8288417855230932627847394045845130135311270668401110, 10724186220799021188186600810422035977226326053145350], ![-257143921906698121897098773540482629245040831756280845, 12130519885967638964425865620209089835309890239026625, -15695390421239578033529333664423868988947281458370859]]]
  hmulB := by decide  
  f := ![![![334954888319605972697690260, -160043704373492990877786873, -130684993053679896407650850]], ![![316454821901749927057306163, -104346026171204431244625644, -91450255092281647916166320]], ![![315357962364928263103526185, -114464777053823564765650088, -98294237265876049315866139]]]
  g := ![![![211220006429631837291889370461633019230816859967644, 772545256427893840672617234892144606455380263618547, -999577885506694260486809487166863304224174472319960], ![-2266119244286310711052364085511050273936857512625457, -8288417855230932627847394045845130135311270668401110, 10724186220799021188186600810422035977226326053145350], ![3316580442362741297324931050387415965217710067404204, 12130519885967638964425865620209089835309890239026625, -15695390421239578033529333664423868988947281458370859]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N1 : Nat.card (O ⧸ I239N1) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N1)

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := prime_ideal_of_norm_prime hp239.out _ NI239N1

def I239N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-282123415545278, -14249772788083, 8230894976934]] i)))

def SI239N2: IdealEqSpanCertificate' Table ![![-282123415545278, -14249772788083, 8230894976934]] 
 ![![239, 0, 0], ![166, 1, 0], ![70, 0, 1]] where
  M :=![![![-282123415545278, -14249772788083, 8230894976934], ![-1454656393751533, -380276981582280, -167190412811632], ![3497879425100473, -60445455690529, -264066782111831]]]
  hmulB := by decide  
  f := ![![![90312618148145948849324521352, -4260411843595473912067368059, 5512445292460768731156510976]], ![![58673457215765679946123070107, -2767864526047650459656529722, 3581273908933684368442835182]], ![![32384827065605180499019247883, -1527723408004510895325870709, 1976684888174911613276204439]]]
  g := ![![![6306176648080, -14249772788083, 8230894976934], ![307006909814733, -380276981582280, -167190412811632], ![133960250282663, -60445455690529, -264066782111831]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N2 : Nat.card (O ⧸ I239N2) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N2)

lemma isPrimeI239N2 : Ideal.IsPrime I239N2 := prime_ideal_of_norm_prime hp239.out _ NI239N2
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![38124440343, 378690009638, 256319449716]] ![![-16376488308475979292971910421248025082253664084475098, 772545256427893840672617234892144606455380263618547, -999577885506694260486809487166863304224174472319960]]
  ![![90312618148145948849324521352, -4260411843595473912067368059, 5512445292460768731156510976]] where
 M := ![![![90312618148145948849324521352, -4260411843595473912067368059, 5512445292460768731156510976]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI239N1 : IdealMulLeCertificate' Table 
  ![![90312618148145948849324521352, -4260411843595473912067368059, 5512445292460768731156510976]] ![![-282123415545278, -14249772788083, 8230894976934]]
  ![![239, 0, 0]] where
 M := ![![![239, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC239 : ContainsPrimesAboveP 239 ![I239N0, I239N1, I239N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI239N0
    exact isPrimeI239N1
    exact isPrimeI239N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 239 (by decide) (𝕀 ⊙ MulI239N0 ⊙ MulI239N1)
instance hp241 : Fact (Nat.Prime 241) := {out := by norm_num}

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-91390894154680971, 21039511320274340, 20195990390782436]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![-91390894154680971, 21039511320274340, 20195990390782436]] 
 ![![241, 0, 0], ![41, 1, 0], ![153, 0, 1]] where
  M :=![![![-91390894154680971, 21039511320274340, 20195990390782436], ![-3513258807066651960, -108212800827495791, 149807142030396092], ![-1218003653372552308, -428333402853890676, -215097399287851299]]]
  hmulB := by decide  
  f := ![![![87443694945344254885998462902020701, -4125073120810000976694156639599076, 5337333746278223086892091290606156]], ![![10983539477342802527564841686668765, -518138025819489230289207644535139, 670406436309014388111858517207648]], ![![61211318837449644751369615657232185, -2887585733694322464485513042781584, 3736178324686754028422799279716769]]]
  g := ![![![-16780072149691459, 21039511320274340, 20195990390782436], ![-91273969725269405, -108212800827495791, 149807142030396092], ![204371651264224955, -428333402853890676, -215097399287851299]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N0 : Nat.card (O ⧸ I241N0) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N0)

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := prime_ideal_of_norm_prime hp241.out _ NI241N0

def I241N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4947901664923454502847916181278234453646622298394263523264230179, 233412553931351268521939938113239030592273982365912309225856970, -302006937675364392001552789921499936770538929893878343712178326]] i)))

def SI241N1: IdealEqSpanCertificate' Table ![![-4947901664923454502847916181278234453646622298394263523264230179, 233412553931351268521939938113239030592273982365912309225856970, -302006937675364392001552789921499936770538929893878343712178326]] 
 ![![241, 0, 0], ![44, 1, 0], ![54, 0, 1]] where
  M :=![![![-4947901664923454502847916181278234453646622298394263523264230179, 233412553931351268521939938113239030592273982365912309225856970, -302006937675364392001552789921499936770538929893878343712178326], ![53084626647120119868793678174375727965436586713794622458857064020, -2504216760821227468752392479217778647424831719461222567799910669, 3240146352339605861224057750896890116234356613340758123395104678], ![-77692043334380927815528929540239822639653696361087812047410725522, 3665048233149073929415144948177803835367252966472491953265568366, -4742118513691415132409077625853451735111827455810365419805266111]]]
  hmulB := by decide  
  f := ![![![1026973656712259054497254162377889, 43961102231864932984557462291646, -35366632784759673682607207945566]], ![![213360841223668905499253120321132, 13750787252139312058792731917447, -4192617933014511581499256858306]], ![![180284877062842097432680869286344, 11286141634512599565000128545310, -3770157352722319926428986845315]]]
  g := ![![![4524151852974136308176668869295621518267322372510478967865945, 233412553931351268521939938113239030592273982365912309225856970, -302006937675364392001552789921499936770538929893878343712178326], ![-48538335697446423287137640201137252383925621370591382660923316, -2504216760821227468752392479217778647424831719461222567799910669, 3240146352339605861224057750896890116234356613340758123395104678], ![71038315960150358673422757410884656847410189742250102399952848, 3665048233149073929415144948177803835367252966472491953265568366, -4742118513691415132409077625853451735111827455810365419805266111]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N1 : Nat.card (O ⧸ I241N1) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N1)

lemma isPrimeI241N1 : Ideal.IsPrime I241N1 := prime_ideal_of_norm_prime hp241.out _ NI241N1

def I241N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1023914150826459, 233074645338686, 94043787285330]] i)))

def SI241N2: IdealEqSpanCertificate' Table ![![1023914150826459, 233074645338686, 94043787285330]] 
 ![![241, 0, 0], ![155, 1, 0], ![42, 0, 1]] where
  M :=![![![1023914150826459, 233074645338686, 94043787285330], ![-16224588129594064, 1485993795754553, 2048615091530870], ![-29314720885459790, -2670073823258710, 42558852954411]]]
  hmulB := by decide  
  f := ![![![5533195721274007267799016060983, -261023244229040565805990368246, 337731751458775986326516629330]], ![![3312370361194839370688386261209, -156257920615922500526913010941, 202178397425076947151745327700]], ![![1324799011251290765956190945156, -62496133028277662722182197902, 80862256269101213410585625351]]]
  g := ![![![-162043547479891, 233074645338686, 94043787285330], ![-1380064150688159, 1485993795754553, 2048615091530870], ![1588212655168278, -2670073823258710, 42558852954411]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N2 : Nat.card (O ⧸ I241N2) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N2)

lemma isPrimeI241N2 : Ideal.IsPrime I241N2 := prime_ideal_of_norm_prime hp241.out _ NI241N2
def MulI241N0 : IdealMulLeCertificate' Table 
  ![![-91390894154680971, 21039511320274340, 20195990390782436]] ![![-4947901664923454502847916181278234453646622298394263523264230179, 233412553931351268521939938113239030592273982365912309225856970, -302006937675364392001552789921499936770538929893878343712178326]]
  ![![-5533195721274007267799016060983, 261023244229040565805990368246, -337731751458775986326516629330]] where
 M := ![![![-5533195721274007267799016060983, 261023244229040565805990368246, -337731751458775986326516629330]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI241N1 : IdealMulLeCertificate' Table 
  ![![-5533195721274007267799016060983, 261023244229040565805990368246, -337731751458775986326516629330]] ![![1023914150826459, 233074645338686, 94043787285330]]
  ![![241, 0, 0]] where
 M := ![![![-241, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC241 : ContainsPrimesAboveP 241 ![I241N0, I241N1, I241N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI241N0
    exact isPrimeI241N1
    exact isPrimeI241N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 241 (by decide) (𝕀 ⊙ MulI241N0 ⊙ MulI241N1)
instance hp251 : Fact (Nat.Prime 251) := {out := by norm_num}

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![251, 0, 0]] 
 ![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]] where
  M :=![![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 3 2 7 [200, 176, 145, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [149, 75, 113], [208, 175, 138], [0, 1]]
 g := ![![[249, 123, 35], [29, 115, 83], [230, 93], [18, 98, 222], [144, 203, 92], [117, 108, 192], [1]], ![[11, 139, 40, 83], [61, 67, 31, 219], [154, 240], [183, 187, 83, 208], [131, 128, 247, 115], [213, 40, 67, 106], [37, 247, 60, 149]], ![[224, 133, 173, 167], [166, 227, 19, 120], [145, 123], [213, 144, 45, 37], [143, 170, 118, 77], [155, 1, 108, 212], [23, 19, 36, 102]]]
 h' := ![![[149, 75, 113], [224, 249, 81], [50, 95, 130], [165, 31, 120], [65, 55, 184], [194, 67, 43], [51, 75, 106], [0, 1]], ![[208, 175, 138], [1, 26, 144], [195, 51, 102], [154, 178, 156], [73, 13, 12], [214, 179, 36], [150, 135, 168], [149, 75, 113]], ![[0, 1], [76, 227, 26], [219, 105, 19], [75, 42, 226], [41, 183, 55], [145, 5, 172], [229, 41, 228], [208, 175, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [181, 32], []]
 b := ![[], [3, 141, 113], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 3
  hpos := by decide
  P := [200, 176, 145, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![24092737, -268821, -597380]
  a := ![2, 9, 20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![95987, -1071, -2380]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 15813251 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def PBC251 : ContainsPrimesAboveP 251 ![I251N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI251N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![251, 0, 0]]) timesTableT_eq_Table B_one_repr 251 (by decide) 𝕀

instance hp257 : Fact (Nat.Prime 257) := {out := by norm_num}

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![257, 0, 0]] 
 ![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]] where
  M :=![![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P0 : CertificateIrreducibleZModOfList' 257 3 2 8 [211, 81, 189, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [55, 227, 43], [13, 29, 214], [0, 1]]
 g := ![![[85, 33, 222], [47, 244], [249, 236], [58, 139], [213, 13], [194, 207], [68, 1], []], ![[30, 144, 169, 3], [95, 144], [161, 193], [148, 79], [243, 162], [56, 246], [29, 70], [49, 50]], ![[35, 179, 230, 10], [160, 89], [254, 133], [73, 118], [112, 89], [113, 208], [14, 129], [135, 50]]]
 h' := ![![[55, 227, 43], [222, 197, 42], [87, 248, 191], [202, 107, 218], [19, 249, 41], [66, 167, 28], [44, 192, 174], [0, 0, 1], [0, 1]], ![[13, 29, 214], [190, 244, 180], [184, 35, 12], [152, 144, 129], [138, 55, 74], [36, 35, 26], [95, 93, 195], [139, 171, 29], [55, 227, 43]], ![[0, 1], [80, 73, 35], [179, 231, 54], [46, 6, 167], [85, 210, 142], [178, 55, 203], [190, 229, 145], [211, 86, 227], [13, 29, 214]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [157, 5], []]
 b := ![[], [136, 144, 227], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 3
  hpos := by decide
  P := [211, 81, 189, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-309503044, -17440020, 2946505]
  a := ![-5, -20, -45]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1204292, -67860, 11465]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N0 B_one_repr
lemma NI257N0 : Nat.card (O ⧸ I257N0) = 16974593 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N0

def PBC257 : ContainsPrimesAboveP 257 ![I257N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI257N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![257, 0, 0]]) timesTableT_eq_Table B_one_repr 257 (by decide) 𝕀



lemma PB259I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 258 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 258 (by omega)

def PB259I4 : PrimesBelowBoundCertificateInterval O 193 258 259 where
  m := 11
  g := ![1, 2, 2, 2, 1, 1, 1, 3, 3, 1, 1]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257]
  hP := PB259I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0]
    · exact ![I199N0, I199N1]
    · exact ![I211N0, I211N1]
    · exact ![I223N0, I223N1]
    · exact ![I227N0]
    · exact ![I229N0]
    · exact ![I233N0]
    · exact ![I239N0, I239N1, I239N2]
    · exact ![I241N0, I241N1, I241N2]
    · exact ![I251N0]
    · exact ![I257N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC197
    · exact PBC199
    · exact PBC211
    · exact PBC223
    · exact PBC227
    · exact PBC229
    · exact PBC233
    · exact PBC239
    · exact PBC241
    · exact PBC251
    · exact PBC257
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![7645373]
    · exact ![39601, 199]
    · exact ![44521, 211]
    · exact ![49729, 223]
    · exact ![11697083]
    · exact ![12008989]
    · exact ![12649337]
    · exact ![239, 239, 239]
    · exact ![241, 241, 241]
    · exact ![15813251]
    · exact ![16974593]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
      exact NI199N1
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
      exact NI211N1
    · dsimp ; intro j
      fin_cases j
      exact NI223N0
      exact NI223N1
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
      exact NI239N1
      exact NI239N2
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
      exact NI241N1
      exact NI241N2
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
    · dsimp ; intro j
      fin_cases j
      exact NI257N0
  β := ![I199N1, I211N1, I223N1, I239N0, I239N1, I239N2, I241N0, I241N1, I241N2]
  Il := ![[], [I199N1], [I211N1], [I223N1], [], [], [], [I239N0, I239N1, I239N2], [I241N0, I241N1, I241N2], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
