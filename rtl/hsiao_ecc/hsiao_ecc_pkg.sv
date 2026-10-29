// Copyright 2024 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Hsiao ECC package
// Based in part on work by lowRISC

package hsiao_ecc_pkg;

  /// Static parameters for synthesizability (avoiding dynamic arrays)
  /// Maximum reasonable Data Width
  localparam int unsigned MaxDataWidth = 1024;
  /// Maximum Width for Parity Bits. For DW=1024 12 bits are needed, but more are always allowed.
  /// We limit to 20 for now.
  localparam int unsigned MaxParityWidth = 20;
  /// Maximum total Width (data + parity)
  localparam int unsigned MaxTotalWidth = MaxDataWidth + MaxParityWidth;
  /// Maximum allowed result for n_choose_k to limit excessive array sizes (20 choose 3).
  localparam int unsigned MaxChoose = 1140;

  function automatic int unsigned min_ecc(int unsigned data_width);
    for (int unsigned i = 0; i < MaxParityWidth; i++) begin
      if (2**i >= data_width + i + 1) begin
        return i + 1;
      end
    end
    $fatal(1, "Data Width too large for MaxParityWidth, please adjust ECC package");
  endfunction

  function automatic int unsigned max_vec(int unsigned vec[MaxParityWidth], int unsigned size);
    max_vec = 0;
    for (int unsigned i = 0; i < size; i++) begin
      max_vec = vec[i] > max_vec ? vec[i] : max_vec;
    end
  endfunction

  function automatic int unsigned min_vec(int unsigned vec[MaxParityWidth], int unsigned size);
    min_vec = vec[0];
    for (int unsigned i = 0; i < size; i++) begin
      min_vec = vec[i] < min_vec ? vec[i] : min_vec;
    end
  endfunction

  function automatic int unsigned factorial(int unsigned i);
    // if (i == 1) begin
    //   factorial = 1;
    // end else begin
    //   factorial = i * factorial(i-1);
    // end
    // return factorial;
    factorial = 1;
    for (int unsigned j = i; j > 0; j--) begin
      factorial = factorial * j;
    end
  endfunction

  function automatic int unsigned n_choose_k(int unsigned n, int unsigned k);
    n_choose_k = 1;
    for (int unsigned i = 0; i < k; i++) begin
      n_choose_k = n_choose_k * (n - i) / (i + 1);
    end
  endfunction

  function automatic int unsigned ideal_fanin(int unsigned k, int unsigned m);
    int unsigned fanin = 0;
    int unsigned needed = k;
    for (int unsigned select = 3; select < m+1; select += 2) begin
      int unsigned combinations = n_choose_k(m, select);
      if (combinations <= needed) begin
        fanin += (combinations*select+(m-1))/m; // ceil(combinations*select/m)
        needed -= combinations;
      end else begin
        fanin += (needed*select+(m-1))/m; // ceil(needed*select/m)
        needed = 0;
      end
      if (needed == 0) break;
    end
    return fanin;
  endfunction

  typedef bit [MaxParityWidth-1:0][MaxTotalWidth-1:0] parity_vec_t;
  typedef bit [MaxTotalWidth-1:0][MaxParityWidth-1:0] parity_vec_trans_t;

  /// Function to generate the Hsiao Code Matrix
  /// k: data bits
  /// m: code bits
  ///
  /// Goal is to find an optimal Hsiao Code Matrix:
  ///   | 1 0 0 0 x x x x |
  ///   | 0 1 0 0 x x x x |
  ///   | 0 0 1 0 x x x x |
  ///   | 0 0 0 1 x x x x |
  /// Then message times matrix => original message with parity
  ///
  /// Columns are kept as parity masks and fan-ins are tracked incrementally; constant evaluation
  /// of this function runs once per encoder/decoder instance, so its cost dominates elaboration.
  function automatic parity_vec_t hsiao_matrix(int unsigned k, int unsigned m);
    parity_vec_t                 existing;
    bit [MaxTotalWidth-1:0]      row;
    bit [MaxParityWidth-1:0]     cols[MaxDataWidth];
    bit [MaxParityWidth-1:0]     combs[MaxChoose];
    bit                          comb_used[MaxChoose];
    int unsigned                 pos[MaxParityWidth];
    int unsigned                 fanins[MaxParityWidth];
    int unsigned total_combinations;

    int unsigned needed      = k;
    int unsigned count_index = 0;
    int unsigned work_fanin  = 0;
    int unsigned min_fanin, max_fanin, min_count;
    int unsigned cand_max, cand_min_hits, pick, next_fanin;
    bit comb_added;

    if (k > MaxDataWidth)
      $fatal(1, "Data Width too large, please adjust package or ECC parameters");
    if (m > MaxParityWidth)
      $fatal(1, "Parity Width too large, please adjust package or ECC parameters");

    for (int unsigned i = 0; i < m; i++) fanins[i] = 0;

    for (int unsigned step = 3; step < m+1; step += 2) begin

      total_combinations = n_choose_k(m, step);
      if (total_combinations > MaxChoose)
        $fatal(1, "Too many combinations, please adjust ECC package MaxChoose");

      // Enumerate all weight-`step` columns in lexicographic order
      for (int unsigned i = 0; i < step; i++) pos[i] = i;
      for (int unsigned i = 0; i < total_combinations; i++) begin
        if (i > 0) begin
          for (int j = step-1; j >= 0; j--) begin
            if (pos[j] + step-j < m) begin
              pos[j]++;
              for (int unsigned l = j+1; l < step; l++) pos[l] = pos[j] + l-j;
              break;
            end
          end
        end
        combs[i] = '0;
        for (int unsigned l = 0; l < step; l++) combs[i][pos[l]] = 1'b1;
      end

      if (total_combinations < needed) begin
        // Add all these combinations
        for (int unsigned i = 0; i < total_combinations; i++) begin
          cols[count_index] = combs[i];
          for (int unsigned l = 0; l < m; l++) fanins[l] += combs[i][l];
          needed--;
          count_index++;
        end
      end else begin
        // Use subset
        for (int unsigned i = 0; i < total_combinations; i++) comb_used[i] = 1'b0;

        while (needed > 0) begin
          min_fanin = fanins[0];
          max_fanin = fanins[0];
          for (int unsigned l = 1; l < m; l++) begin
            if (fanins[l] < min_fanin) min_fanin = fanins[l];
            if (fanins[l] > max_fanin) max_fanin = fanins[l];
          end
          min_count = 0;
          for (int unsigned l = 0; l < m; l++) min_count += (fanins[l] == min_fanin);

          // First add to increase minimum (cover every row at min_fanin) while keeping max low,
          // then add to increase maximum. If nothing fits, nothing can until work_fanin reaches
          // the smallest candidate maximum, so jump there directly.
          comb_added = 0;
          next_fanin = '1;
          for (int unsigned pass = 0; pass < 2 && !comb_added; pass++) begin
            for (int unsigned i = 0; i < total_combinations; i++) begin
              if (comb_used[i]) continue;
              cand_max      = max_fanin;
              cand_min_hits = 0;
              for (int unsigned l = 0; l < m; l++) begin
                if (combs[i][l]) begin
                  if (fanins[l] + 1 > cand_max) cand_max = fanins[l] + 1;
                  cand_min_hits += (fanins[l] == min_fanin);
                end
              end
              if (cand_max < next_fanin) next_fanin = cand_max;
              if ((pass == 1 || cand_min_hits == min_count) && cand_max <= work_fanin) begin
                comb_added = 1;
                pick       = i;
                break;
              end
            end
          end

          if (comb_added) begin
            cols[count_index] = combs[pick];
            comb_used[pick]   = 1'b1;
            for (int unsigned l = 0; l < m; l++) fanins[l] += combs[pick][l];
            needed--;
            count_index++;
          end else begin
            work_fanin = next_fanin;
          end
        end
        break;
      end
    end

    if (count_index != k) $error("did not fill all parity bits!");

    existing = '0;
    for (int unsigned i = 0; i < m; i++) begin
      row = '0;
      for (int unsigned j = 0; j < k; j++) row[j] = cols[j][i];
      row[k+i] = 1'b1;
      existing[i] = row;
    end

    hsiao_matrix = existing;
  endfunction

  function automatic parity_vec_trans_t transpose(
    parity_vec_t matrix,
    int unsigned m,
    int unsigned n
  );
    for (int unsigned i = 0; i < m; i++) begin
      for (int unsigned j = 0; j < n; j++) begin
        transpose[j][i] = matrix[i][j];
      end
    end
  endfunction

endpackage
