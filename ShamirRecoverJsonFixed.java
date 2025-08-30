import java.io.*;
import java.math.BigInteger;
import java.util.*;
import java.util.regex.*;

public class ShamirRecoverJsonFixed {
    static class BigFraction {
        BigInteger num, den;
        BigFraction(BigInteger n, BigInteger d) {
            if (d.signum() == 0) throw new ArithmeticException("zero denominator");
            if (d.signum() < 0) { n = n.negate(); d = d.negate(); }
            BigInteger g = n.gcd(d);
            if (!g.equals(BigInteger.ONE)) { n = n.divide(g); d = d.divide(g); }
            this.num = n; this.den = d;
        }
        BigFraction(long v){ this(BigInteger.valueOf(v), BigInteger.ONE); }
        static BigFraction zero(){ return new BigFraction(BigInteger.ZERO, BigInteger.ONE); }
        static BigFraction one(){ return new BigFraction(BigInteger.ONE, BigInteger.ONE); }
        BigFraction add(BigFraction o){ return new BigFraction(this.num.multiply(o.den).add(o.num.multiply(this.den)), this.den.multiply(o.den)); }
        BigFraction sub(BigFraction o){ return new BigFraction(this.num.multiply(o.den).subtract(o.num.multiply(this.den)), this.den.multiply(o.den)); }
        BigFraction mul(BigFraction o){ return new BigFraction(this.num.multiply(o.num), this.den.multiply(o.den)); }
        BigFraction mul(BigInteger b){ return new BigFraction(this.num.multiply(b), this.den); }
        BigFraction div(BigFraction o){ if (o.num.equals(BigInteger.ZERO)) throw new ArithmeticException("div zero"); return new BigFraction(this.num.multiply(o.den), this.den.multiply(o.num)); }
        boolean equalsBF(BigFraction o){ return this.num.equals(o.num) && this.den.equals(o.den); }
        public String toString(){ return den.equals(BigInteger.ONE) ? num.toString() : (num.toString() + "/" + den.toString()); }
    }

    static class InputData { int n; int k; LinkedHashMap<Integer,Share> shares = new LinkedHashMap<>(); }
    static class Share { int key; int x; BigInteger y; Share(int key, int x, BigInteger y){ this.key=key; this.x=x; this.y=y; } }
    static class PolyRec { BigFraction[] coeffs; int matches; boolean[] matchesMask; PolyRec(BigFraction[] c,int m,boolean[] mask){ coeffs=c; matches=m; matchesMask=mask;} }

    public static void main(String[] args) throws Exception {
        String raw = readAllStdIn();
        if (raw.trim().isEmpty()) { System.err.println("{\"error\":\"empty_input\"}"); return; }
        InputData data = parseInput(raw);
        if (data == null) { System.err.println("{\"error\":\"failed_to_parse_input\"}"); return; }
        int n = data.n, k = data.k;
        if (k < 1 || k > n) { System.err.println("{\"error\":\"invalid_k_or_n\"}"); return; }
        List<Share> shareList = new ArrayList<>();
        for (Map.Entry<Integer,Share> e : data.shares.entrySet()) shareList.add(e.getValue());
        int m = shareList.size();
        if (m < k) { System.err.println("{\"error\":\"not_enough_shares\"}"); return; }
        Set<Integer> xset = new HashSet<>();
        for (Share s : shareList) {
            if (xset.contains(s.x)) { System.err.println("{\"error\":\"duplicate_x_values\"}"); return; }
            xset.add(s.x);
        }
        List<int[]> combos = new ArrayList<>();
        generateCombos(m, k, 0, new int[k], combos);
        Map<String,PolyRec> polyMap = new HashMap<>();
        PolyRec best = null;
        for (int[] comb : combos) {
            List<Share> pts = new ArrayList<>(k);
            for (int idx : comb) pts.add(shareList.get(idx));
            BigFraction[] coeffs = lagrangePoly(pts);
            if (coeffs == null) continue;
            String sig = polySignature(coeffs);
            if (polyMap.containsKey(sig)) {
                PolyRec r = polyMap.get(sig);
                if (best == null || r.matches > best.matches) best = r;
                if (best != null && best.matches == m) break;
                continue;
            }
            boolean[] mask = new boolean[m];
            int matches = 0;
            for (int i = 0; i < m; ++i) {
                Share s = shareList.get(i);
                BigFraction got = evaluate(coeffs, s.x);
                BigFraction actual = new BigFraction(s.y, BigInteger.ONE);
                if (got.equalsBF(actual)) { mask[i] = true; matches++; } else mask[i]=false;
            }
            PolyRec rec = new PolyRec(coeffs, matches, mask);
            polyMap.put(sig, rec);
            if (best == null || rec.matches > best.matches) best = rec;
            if (best.matches == m) break;
        }
        if (best == null) { System.err.println("{\"error\":\"no_valid_polynomial\"}"); return; }
        BigFraction secret = best.coeffs[0];
        String secretStr = secret.toString();
        List<Integer> wrongKeys = new ArrayList<>();
        int idx = 0;
        for (Map.Entry<Integer,Share> e : data.shares.entrySet()) {
            if (!best.matchesMask[idx]) wrongKeys.add(e.getKey());
            idx++;
        }
        StringBuilder out = new StringBuilder();
        out.append("{\n");
        out.append("  \"secret\": \"" + escapeJson(secretStr) + "\",\n");
        out.append("  \"wrong_shares\": [");
        for (int i = 0; i < wrongKeys.size(); ++i) {
            if (i > 0) out.append(", ");
            out.append(wrongKeys.get(i));
        }
        out.append("]\n");
        out.append("}");
        System.out.println(out.toString());
    }

    static BigFraction evaluate(BigFraction[] coeffs, int x) {
        BigFraction res = BigFraction.zero();
        BigFraction pow = BigFraction.one();
        BigFraction bx = new BigFraction(BigInteger.valueOf(x), BigInteger.ONE);
        for (BigFraction c : coeffs) {
            res = res.add(c.mul(pow));
            pow = pow.mul(bx);
        }
        return res;
    }

    static BigFraction[] lagrangePoly(List<Share> pts) {
        int k = pts.size();
        BigFraction[] coeffs = new BigFraction[k];
        for (int i=0;i<k;i++) coeffs[i] = BigFraction.zero();
        BigInteger[] xi = new BigInteger[k];
        BigInteger[] yi = new BigInteger[k];
        for (int i=0;i<k;i++){ xi[i]=BigInteger.valueOf(pts.get(i).x); yi[i]=pts.get(i).y; }
        for (int i=0;i<k;i++) {
            BigFraction[] poly = new BigFraction[1];
            poly[0] = BigFraction.one();
            for (int j=0;j<k;j++) if (j!=i) {
                BigFraction[] next = new BigFraction[poly.length + 1];
                for (int a=0;a<next.length;a++) next[a]=BigFraction.zero();
                BigFraction negXj = new BigFraction(xi[j].negate(), BigInteger.ONE);
                BigFraction one = BigFraction.one();
                for (int a=0;a<poly.length;a++) {
                    next[a] = next[a].add(poly[a].mul(negXj));
                    next[a+1] = next[a+1].add(poly[a].mul(one));
                }
                poly = next;
            }
            BigInteger denom = BigInteger.ONE;
            for (int j=0;j<k;j++) if (j!=i) {
                BigInteger diff = xi[i].subtract(xi[j]);
                if (diff.equals(BigInteger.ZERO)) return null;
                denom = denom.multiply(diff);
            }
            BigFraction factor = new BigFraction(yi[i], denom);
            for (int c=0;c<poly.length;c++) {
                coeffs[c] = coeffs[c].add(poly[c].mul(factor));
            }
        }
        return coeffs;
    }

    static String polySignature(BigFraction[] coeffs) {
        StringBuilder sb = new StringBuilder();
        for (BigFraction f : coeffs) { sb.append(f.num.toString()).append("/").append(f.den.toString()).append("|"); }
        return sb.toString();
    }

    static void generateCombos(int n, int k, int start, int[] cur, List<int[]> out) {
        if (k==0) { out.add(cur.clone()); return; }
        for (int i=start;i<=n-k;i++) { cur[cur.length-k] = i; generateCombos(n,k-1,i+1,cur,out); }
    }

    static InputData parseInput(String s) {
        InputData data = new InputData();
        Pattern keysPat = Pattern.compile("\"keys\"\\s*:\\s*\\{([^}]*)\\}", Pattern.DOTALL);
        Matcher mKeys = keysPat.matcher(s);
        if (!mKeys.find()) return null;
        String keysBlock = mKeys.group(1);
        Pattern nPat = Pattern.compile("\"n\"\\s*:\\s*(\\d+)");
        Pattern kPat = Pattern.compile("\"k\"\\s*:\\s*(\\d+)");
        Matcher mn = nPat.matcher(keysBlock), mk = kPat.matcher(keysBlock);
        if (!mn.find() || !mk.find()) return null;
        data.n = Integer.parseInt(mn.group(1));
        data.k = Integer.parseInt(mk.group(1));
        Pattern sharePat = Pattern.compile("\"(\\d+)\"\\s*:\\s*\\{[^}]*?\"base\"\\s*:\\s*\"([^\"]+)\"[^}]*?\"value\"\\s*:\\s*\"([^\"]+)\"[^}]*?\\}", Pattern.DOTALL);
        Matcher ms = sharePat.matcher(s);
        Set<Integer> seenKeys = new HashSet<>();
        while (ms.find()) {
            int key = Integer.parseInt(ms.group(1));
            if (seenKeys.contains(key)) return null;
            seenKeys.add(key);
            String baseStr = ms.group(2).trim();
            String valStr = ms.group(3).trim();
            int base;
            try { base = Integer.parseInt(baseStr); }
            catch (Exception e) { return null; }
            BigInteger y;
            try { y = new BigInteger(valStr.toUpperCase(), base); }
            catch (Exception ex) { return null; }
            int xCoord = key;
            data.shares.put(key, new Share(key, xCoord, y));
        }
        if (data.shares.size() < data.k) return null;
        return data;
    }

    static String readAllStdIn() throws IOException {
        BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
        StringBuilder sb = new StringBuilder();
        String line;
        while ((line = br.readLine()) != null) { sb.append(line).append("\n"); }
        return sb.toString();
    }

    static String escapeJson(String s) {
        return s.replace("\\", "\\\\").replace("\"", "\\\"");
    }
}
