package ss.othello.game.model;


import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Board for the Othello game.
 * Players place marks on this board, trying to
 * capture opponent pieces and flip them to their own
 * markers.
 */
public class Board {
    /*@
        private invariant fields.length == DIM * DIM;
        private invariant (\forall int i; (i >= 0 && i < DIM * DIM);
        fields[i] == Mark.EMPTY || fields[i] == Mark.WW || fields[i] == Mark.BB);
    @*/

    /**
     * Dimension of the board, the board has 8 rows and 8 columns.
     */
    private static final int DIM = 8;
    private static final String DELIM = "     ";
    private static final String[] NUMBERING = {
        " 1  | 00 | 01 | 02 | 03 | 04 | 05 | 06 | 07 |",
        "      ----+----+----+----+----+----+----+----",
        " 2  | 08 | 09 | 10 | 11 | 12 | 13 | 14 | 15 |",
        "      ----+----+----+----+----+----+----+----",
        " 3  | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 |",
        "      ----+----+----+----+----+----+----+----",
        " 4  | 24 | 25 | 26 | WW | BB | 29 | 30 | 31 |",
        "      ----+----+----+----+----+----+----+----",
        " 5  | 32 | 33 | 34 | BB | WW | 37 | 38 | 39 |",
        "      ----+----+----+----+----+----+----+----",
        " 6  | 40 | 41 | 42 | 43 | 44 | 45 | 46 | 47 |",
        "      ----+----+----+----+----+----+----+----",
        " 7  | 48 | 49 | 50 | 51 | 52 | 53 | 54 | 55 |",
        "      ----+----+----+----+----+----+----+----",
        " 8  | 56 | 57 | 58 | 59 | 60 | 61 | 62 | 63 |",

    };


    private static final String LINE = "   ----+----+----+----+----+----+----+----";
    /**
     * The DIM by DIM fields of the Othello board. See NUMBERING for the
     * coding of the fields.
     */
    private final Mark[] fields;
    private int[][] adjacent = {{-1, -1}, {0, -1}, {1, -1},
        {-1, 0}, {1, 0}, {-1, 1}, {0, 1}, {1, 1}}; // 8 directions to check

    // -- Constructors -----------------------------------------------

    /**
     * Creates an empty board.
     * The board has 64 fields. On the field 27, 36 the mark white is present
     * and on 28, 35 the mark black is present.
     */
    //@ ensures (\forall int i; (i >= 0 && i < DIM*DIM); fields[i] == Mark.EMPTY);
    public Board() {
        fields = new Mark[DIM * DIM];
        for (int i = 0; i < DIM * DIM; i++) {
            fields[i] = Mark.EMPTY;
        }
        fields[27] = Mark.WW;
        fields[36] = Mark.WW;
        fields[28] = Mark.BB;
        fields[35] = Mark.BB;
    }


    /**
     * Getter for the constant DIM that represents
     * the dimension of the board on an axis.
     *
     * @return Dimension of the board.
     */
    /*@ensures \result == this.DIM;
        pure
    */
    public int getDim() {
        return DIM;
    }


    /**
     * Calculates the index in the linear array of fields from a (row, col)
     * pair.
     *
     * @param row row number of the board
     * @param col column number of the board
     * @return the index belonging to the (row,col)-field
     */
    /*@ requires row >= 0 && row < DIM;
        requires col >= 0 && col < DIM;
        pure
     @*/
    public int index(int row, int col) {
        if (row >= 0 && row < DIM && col >= 0 && col < DIM) {
            return row * DIM + col;
        }
        return -1;
    }

    /**
     * Returns true if index is a valid index of a field on the board.
     *
     * @param index the index of the field (see NUMBERING)
     * @return true if index is between 0 (inclusive) and DIM squared (exclusive)
     */
    /*@
        ensures index >= 0 && index < DIM * DIM ==> \result == true;
        pure
    */
    public boolean isField(int index) {
        return index >= 0 && index < DIM * DIM;
    }

    /**
     * Returns true if the (row,col) pair refers to a valid field on the board.
     *
     * @param row A row of the board
     * @param col A column of the board
     * @return true if row is between 0 (inclusive) and
     * DIM (exclusive) and col is between 0 (inclusive) and DIM (exclusive)
     */
    /*@
        ensures row >= 0 && row < DIM && col >= 0 && col < DIM ==> \result == true;
        pure
    */
    public boolean isField(int row, int col) {
        //if there exists such an index, then the field is valid.
        return index(row, col) >= 0;

    }

    /**
     * Returns the content of the field i.
     *
     * @param i the number of the field (see NUMBERING)
     * @return the mark on the field
     */
    /*@
        requires isField(i);
        requires i >= 0 && i < 64;
        ensures \result == Mark.EMPTY || \result == Mark.BB || \result == Mark.WW;
        pure
     */
    public Mark getField(int i) {
        if (isField(i)) {
            return fields[i];
        }
        return null;
    }

    /**
     * Returns the content of the field referred to by the (row,col) pair.
     *
     * @param row the row of the field
     * @param col the column of the field
     * @return the mark on the field, otherwise null if the field is not valid.
     */
    /*@
        requires isField(row, col);
        ensures \result == Mark.EMPTY || \result == Mark.BB || \result == Mark.WW;
        pure
    */
    public Mark getField(int row, int col) {
        if (isField(row, col)) {
            return fields[index(row, col)];
        }
        return null;
    }

    /**
     * Returns true if the field index is empty.
     *
     * @param index the index of the field (see NUMBERING)
     * @return true if the field is empty
     */
    /*@
        requires isField(index);
        ensures getField(index) == Mark.EMPTY ==> \result == true;
        pure
     */
    public boolean isEmptyField(int index) {
        if (isField(index)) {
            return getField(index) == Mark.EMPTY;
        }
        return false;
    }

    /**
     * Tests if the whole board is full.
     *
     * @return true if all fields are occupied
     */
    /*@
        ensures (\forall int i; (i >= 0 && i < DIM * DIM);
        fields[i] == Mark.WW || fields[i] == Mark.BB);
        pure
    */
    public boolean isFull() {
        for (int i = 0; i < DIM * DIM; i++) {
            if (fields[i] == Mark.EMPTY) {
                return false;
            }
        }
        return true;
    }


    /**
     * Returns true if the game is over. The game is over when the board is full
     * or when there are no moves possible for both players.
     *
     * @return true if the game is over
     */
    /*@
        ensures isFull() || !gamePossible() ==> \result == true;
        pure;
    */
    public boolean gameOver() {
        return isFull() || !gamePossible();
    }


    /**
     * Checks if the game can continue. If one mark
     * has possible moves on the current board, then the game can continue.
     *
     * @return true if one mark has moves on the current board, otherwise false.
     */
    /*@
        ensures calculateValidMoves(Mark.WW).size() != 0
        || calculateValidMoves(Mark.BB).size() != 0 ==> \result == true;
        pure
    */
    public boolean gamePossible() {
        return !calculateValidMoves(Mark.WW).isEmpty() || !calculateValidMoves(Mark.BB).isEmpty();
    }


    /**
     * Maps all the fields that are occupied by the current mark (the keys in the map),
     * to a list of all the adjacent opponent's mark.
     *
     * @param m Mark of the current player.
     * @return Map that contains as key the current mark index and the value is a list
     * containing all the adjacent fields of this mark, that are occupied by an opponent's mark.
     */
    /*@
        requires m != null;
        requires m == Mark.BB || m == Mark.WW;
        ensures (\forall int i; isField(i) && getField(i) == m ==> \result.containsKey(i));
        ensures (\forall int i, j; isField(i) && j < adjacent.length;
        getField(i / DIM + adjacent[j][0],
        i % DIM + adjacent[j][1]) == m.other() ==> \result.get(i).size() != 0);
        ensures (\forall int i, j ; isField(i) && j < adjacent.length;
        getField(i / DIM + adjacent[j][0],
        i % DIM + adjacent[j][1])== m.other() ==>
        \result.get(i).contains(getField(i / DIM + adjacent[j][0],
        i % DIM + adjacent[j][1])));
        pure
    */
    public Map<Integer, List<Integer>> getAdjacentEnemies(Mark m) {
        int row;
        int col;
        //map the current mark index to a list of the opponent's adjacent indexes
        Map<Integer, List<Integer>> mapFields = new HashMap<>();
        //list for putting the adjacent opponent's fields
        List<Integer> opponents;
        for (int i = 0; i < DIM * DIM; i++) {
            if (isEmptyField(i)) {
                row = i / DIM;
                col = i % DIM;
                opponents = new ArrayList<>();
                for (int j = 0; j < adjacent.length; j++) {
                    //if i has an adjacent field that contains an opponent mark
                    if (isField(row + adjacent[j][0], col + adjacent[j][1])
                            && getField(row + adjacent[j][0], col + adjacent[j][1]) == m.other()) {
                        opponents.add(index(row + adjacent[j][0], col + adjacent[j][1]));
                    }
                }
                mapFields.put(i, opponents);
            }
        }
        return mapFields;
    }


    /**
     * A move is valid only if the current mark is placed on an empty field that is
     * adjacent to an opponent's mark, such that there is a mark of the same color on the row,
     * diag or col and there are pieces of the opponent's mark in between those two current marks.
     *
     * @param mark of the current player.
     * @return a map where the key is a valid field for this mark and the value
     * is a list containing all the first found marks of the same color as this current mark,
     * placed on a row, diag or col. The map is used to know from and until where to flip.
     */
    /*@
        requires mark != null;
        requires mark == Mark.BB || mark == Mark.WW;
        pure
    */
    public Map<Integer, List<Integer>> calculateValidMoves(Mark mark) {
        int row;
        int col;
        int rowEnemy;
        int colEnemy;
        Map<Integer, List<Integer>> map = getAdjacentEnemies(mark);
        /*
        map that contains the valid fields
        of the current mark mapped to a list of the first same color mark
        indices that have the opponent's marks in between.
        */
        Map<Integer, List<Integer>> toTurn = new HashMap<>();
        List<Integer> success;
        for (Integer key : map.keySet()) {
            row = key / DIM;
            col = key % DIM;
            //initialize it here, so for each key we get a new list
            success = new ArrayList<>();
            for (Integer value : map.get(key)) {
                rowEnemy = value / DIM;
                colEnemy = value % DIM;
                if (row == rowEnemy) {
                    //if the list is empty then no successful results were found
                    if (!checkRow(key, value, mark).isEmpty()) {
                        success.addAll(checkRow(key, value, mark));
                    }
                }
                if (col == colEnemy) {
                    if (!checkColumn(key, value, mark).isEmpty()) {
                        success.addAll(checkColumn(key, value, mark));
                    }
                }
                if (row != rowEnemy && col != colEnemy) {
                    if (!checkDiagonal(key, value, mark).isEmpty()) {
                        success.addAll(checkDiagonal(key, value, mark));
                    }
                }
            }
            if (success.size() != 0) {
                toTurn.put(key, success);
            }
        }

        return toTurn;
    }


    /**
     * Check if there are 2 marks of the same color on a diagonal, such that they
     * have in between only opponent's pieces. There are 2 possible diagonals to check.
     *
     * @param possibleField the field where the current mark wants to be placed.
     * @param opponentField the adjacent field, where the opponent mark is placed.
     * @param m             - mark of this current player.
     * @return a list that contains the first same color marks as this current mark,
     * found on the same diagonal and in between them there are only opponent's marks.
     */
    /*@
        requires m != null;
        requires m == Mark.BB || m == Mark.WW;
        requires isField(possibleField) && isField(opponentField);
        ensures (\forall int i ; i >= opponentField + 9  && i < DIM * DIM; getField(i) == m ==>
            \result.contains(i));
        ensures (\forall int i ; i >= opponentField - 9  && i != -1; getField(i) == m ==>
            \result.contains(i));
        ensures (\forall int i ; i >= opponentField - 7  && i != -1; getField(i) == m ==>
            \result.contains(i));
        ensures (\forall int i ; i >= opponentField + 7  && i != -1; getField(i) == m ==>
            \result.contains(i));
        pure
    */
    public List<Integer> checkDiagonal(int possibleField, int opponentField, Mark m) {
        int row = possibleField / DIM;
        int col = possibleField % DIM;
        int opponentRow = opponentField / DIM;
        int opponentCol = opponentField % DIM;
        List<Integer> flipDiag = new ArrayList<>();
        if (row < opponentRow && col < opponentCol && opponentCol != 7 && opponentRow != 7) {
            //in case is diagonal down - right
            for (int i = opponentField + 9; i < DIM * DIM; i += 9) {
                if (isField(i) && i % DIM != 0 && getField(i) != Mark.EMPTY) {
                    if (getField(i) == m && flipDiag.add(i)) {
                        break;
                    }
                } else {
                    break;
                }
            }
        }
        if (row > opponentRow && col > opponentCol && opponentRow != 0 && opponentCol != 0) {
            //in case is diagonal up - left
            for (int i = opponentField - 9; i != -1; i -= 9) {
                if (isField(i) && i % DIM != 7 && getField(i) != Mark.EMPTY) {
                    if (getField(i) == m && flipDiag.add(i)) {
                        break;
                    }
                } else {
                    break;
                }
            }
        }
        if (row > opponentRow && col < opponentCol && opponentRow != 0 && opponentCol != 7) {
            //in case is diagonal up - right
            for (int i = opponentField - 7; i != -1; i -= 7) {
                if (isField(i) && i % DIM != 0 && getField(i) != Mark.EMPTY) {
                    if (getField(i) == m && flipDiag.add(i)) {
                        break;
                    }
                } else {
                    break;
                }
            }
        }
        if (row < opponentRow && col > opponentCol && opponentRow != 7 && opponentCol != 0) {
            //in case is diagonal down - left
            for (int i = opponentField + 7; i != -1; i += 7) {
                if (isField(i) && i % DIM != 7 && getField(i) != Mark.EMPTY) {
                    if (getField(i) == m && flipDiag.add(i)) {
                        break;
                    }
                } else {
                    break;
                }
            }
        }
        return flipDiag;
    }


    /**
     * Checks if there are 2 marks of the same color on a column, such that they
     * have in between only opponent's pieces.
     *
     * @param possibleField the field where the current mark wants to be placed.
     * @param opponentField the adjacent field, where the opponent mark is placed.
     * @param m             - mark of this current player.
     * @return a list that contains the first same color marks as this current mark,
     * found on the same column and in between them there are only opponent's marks.
     */
    /*@
        requires m != null;
        requires m == Mark.BB || m == Mark.WW;
        requires isField(possibleField)
        && isField(opponentField);
        ensures (\forall int i ; i >= opponentField / DIM + 1 && i < DIM;
        getField(i, possibleField % DIM)
        == m ==> \result.contains(index(i, possibleField % DIM)));
        ensures (\forall int i ; i >= opponentField / DIM - 1 && i != -1;
        getField(i, possibleField % DIM)
        == m ==> \result.contains(index(i, possibleField % DIM )));
        pure
    */
    public List<Integer> checkColumn(int possibleField, int opponentField, Mark m) {
        int col = possibleField % DIM;
        int row = possibleField / DIM;
        int opponentRow = opponentField / DIM;
        List<Integer> flipCol = new ArrayList<>();
        //need a list instead not just returning, in the case the col has 2 possibilities.
        if (row < opponentRow && opponentRow != 7) {
            for (int i = opponentRow + 1; i < DIM; i++) {
                if (getField(i, col) != Mark.EMPTY) {
                    if (getField(i, col) == m && flipCol.add(index(i, col))) {
                        break;
                    }
                } else {
                    break;
                }
            }
        }
        if (row > opponentRow && opponentRow != 0) {
            for (int i = opponentRow - 1; i != -1; i--) {
                if (getField(i, col) != Mark.EMPTY) {
                    if (getField(i, col) == m && flipCol.add(index(i, col))) {
                        break;
                    }
                } else {
                    break;
                }
            }
        }
        return flipCol;
    }

    /**
     * Check if there are 2 marks of the same color on a row, such that they
     * have in between only opponent's pieces.
     *
     * @param possibleField the field where the current mark wants to be placed.
     * @param opponentField the adjacent field, where the opponent mark is placed.
     * @param m             - mark of this current player.
     * @return a list that contains the first same color marks as this current mark,
     * found on the same row and in between them there are only opponent's marks.
     */
    /*@
        requires m != null;
        requires m == Mark.BB || m == Mark.WW;
        requires isField(possibleField) && isField(opponentField);
        ensures (\forall int i ; i >= opponentField % DIM + 1 && i < DIM;
        getField(possibleField / DIM, i)
        == m ==> \result.contains(index(possibleField / DIM , i)));
        ensures (\forall int i ; i >= opponentField % DIM - 1 && i != -1;
        getField(possibleField / DIM, i)
        == m ==> \result.contains(index(possibleField / DIM , i)));
        pure
    */
    public List<Integer> checkRow(int possibleField, int opponentField, Mark m) {
        int row = possibleField / DIM;
        int col = possibleField % DIM;
        int opponentCol = opponentField % DIM;
        List<Integer> flipRow = new ArrayList<>();
        if (col < opponentCol && opponentCol != 7) {
            for (int i = opponentCol + 1; i < DIM; i++) {
                if (getField(row, i) != Mark.EMPTY) {
                    if (getField(row, i) == m) {
                        flipRow.add(index(row, i));
                        break;
                    }
                } else {
                    break;
                }
            }
        }
        if (col > opponentCol && opponentCol != 0) {
            for (int i = opponentCol - 1; i != -1; i--) {
                if (getField(row, i) != Mark.EMPTY) {
                    if (getField(row, i) == m) {
                        flipRow.add(index(row, i));
                        break;
                    }
                } else {
                    break;
                }
            }
        }
        return flipRow;
    }


    /**
     * Checks if the mark m has won.
     * It will check if the mark is the winner only if the board is full or no more
     * moves are possible for both players. A marks has won if it has more pieces of its color
     * on the board.
     *
     * @param m the mark of interest
     * @return true if the mark has won
     */
    /*@
        requires m == Mark.WW || m == Mark.BB;
        ensures countMarker(m) > countMarker(m.other()) ==> \result == true;
        pure
     @*/
    public boolean isWinner(Mark m) {
        int countCurrent;
        int countOpponent;
        if (gameOver()) {
            if (m == Mark.WW || m == Mark.BB) {
                countCurrent = countMarker(m);
                countOpponent = countMarker(m.other());
                //winner only if more pieces
                return countCurrent > countOpponent;
            }
        }
        return false;
    }

    /**
     * Counts how many pieces a marker has on the board.
     *
     * @param m Mark to check
     * @return number of pieces of the marker
     */
    /*@
        requires m == Mark.BB || m == Mark.WW;
        ensures \result == (\num_of int i; i >= 0 && i < DIM * DIM; getField(i) == m);
        pure
    */
    public int countMarker(Mark m) {
        int result = 0;
        for (int i = 0; i < DIM * DIM; i++) {
            if (getField(i) == m) {
                result++;
            }
        }
        return result;
    }


    /**
     * Returns true if the game has a winner. This is the case when a mark
     * has more pieces of its color on the board. If both have the same
     * number of pieces, then it is a draw.
     *
     * @return true if the game has a winner, false if it's a draw.
     */
    /*@
        ensures isWinner(Mark.WW) || isWinner(Mark.BB) ==> \result == true;
        pure
    */
    public boolean hasWinner() {
        return isWinner(Mark.WW) || isWinner(Mark.BB);
    }

    /**
     * Returns a String representation of this board. In addition to the current
     * situation, the String also shows the numbering of the fields.
     *
     * @return the board situation as String
     */
    public String toString() {
        String ansiBlack = "\u001B[30;1m";
        String ansiReset = "\u001B[0m";
        String ansiBrown = "\u001B[37m";
        String alphabet = " A    B    C    D    E    F    G    H  ";
        String[] numbers = {"1", "2", "3", "4", "5", "6", "7", "8"};
        String s = "";
        for (int i = 0; i < DIM; i++) {
            String row = "";
            for (int j = 0; j < DIM; j++) {
                if (getField(i, j).toString().charAt(0) == 'E') {
                    row += " " + getField(i, j).toString().substring(0, 1).
                            replace("E", "  ") + " ";
                }
                if (getField(i, j).toString().charAt(0) == 'W') {
                    row += " " + getField(i, j).toString().substring(0, 1).
                            replace("W", ansiReset + "WW") + ansiReset + " ";
                }
                if (getField(i, j).toString().charAt(0) == 'B') {
                    row += " " + getField(i, j).toString().substring(0, 1).
                            replace("B", ansiBlack + "BB") + ansiReset + " ";
                }
                if (j < DIM - 1) {
                    row = row + ansiBrown + "|" + ansiReset;
                }
            }
            s = s + numbers[i] + ansiBrown + " |" + row +
                    ansiBrown + "|" + ansiReset + DELIM + NUMBERING[i * 2];
            if (i < DIM - 1) {
                s = s + "\n" + ansiBrown + LINE + DELIM + ansiReset + NUMBERING[i * 2 + 1] + "\n";
            }
        }
        return "   " + alphabet + "           " + alphabet + "\n" + s;
    }


    /**
     * Sets the content of field i to the mark m.
     *
     * @param i the field number (see NUMBERING)
     * @param m the mark to be placed
     */
    /*@
        requires isField(i);
        requires m != null;
        ensures getField(i) == m;
     */
    public void setField(int i, Mark m) {
        if (isField(i)) {
            fields[i] = m;
        }
    }


}
