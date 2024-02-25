package ss.othello.test;


import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import ss.othello.game.model.Board;
import ss.othello.game.model.Mark;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;


/**
 * Test for the board class. Test the methods from the class,
 * the game over conditions, valid moves.
 */
class BoardTest {


    private Board board;

    /**
     * Will be run before every test.
     */
    @BeforeEach
    public void setUp() {
        board = new Board();
    }

    /**
     * Tests the indexes of the board.
     * The index is a number from 0 until 63.
     */
    @Test
    public void testIndex() {
        for (int k = 0; k < board.getDim(); k++) {
            for (int j = 0; j < board.getDim(); j++) {
                assertEquals(board.getDim() * k + j, board.index(k, j));
            }
        }
    }

    /**
     * Test if the index in the linear array of fields
     * is valid. Test for isField(int index).
     * The index is valid if it is 0 <= index < 64.
     */
    @Test
    public void testIsFieldIndex() {
        for (int i = 0; i < board.getDim() * board.getDim(); i++) {
            assertTrue(board.isField(i));
        }
        assertFalse(board.isField(-1));
        assertFalse(board.isField(100));
        assertFalse(board.isField(-100));
        assertFalse(board.isField(66));
        assertFalse(board.isField(-2));
        assertFalse(board.isField(64));
        assertFalse(board.isField(65));
    }

    /**
     * Test if the index in the linear array of fields from a (row, col).
     * is valid. Test for the method isField(int row, int col)
     * The index is valid if it is 0 <= index < 64
     */
    @Test
    public void testIsFieldRowCol() {
        for (int i = 0; i < board.getDim(); i++) {
            for (int j = 0; j < board.getDim(); j++) {
                assertTrue(board.isField(i, j));
            }
        }
    }

    /**
     * Test if the mark is placed on the specified field.
     * Test for the method setField(int i, Mark m).
     */
    @Test
    public void testSetAndGetFieldIndex() {
        board.setField(1, Mark.BB);
        assertEquals(Mark.BB, board.getField(1));
        board.setField(15, Mark.WW);
        assertEquals(Mark.WW, board.getField(15));
        assertEquals(Mark.EMPTY, board.getField(0));
        board.setField(63, Mark.WW);
        assertEquals(Mark.WW, board.getField(63));
        board.setField(5, Mark.BB);
        assertEquals(Mark.BB, board.getField(5));
        board.setField(10, Mark.WW);
        assertEquals(Mark.WW, board.getField(10));
        board.setField(5, Mark.WW);
        assertEquals(Mark.WW, board.getField(5));
        assertEquals(Mark.EMPTY, board.getField(60));
    }

    /**
     * Test if the board is EMPTY at the beginning,
     * except for the fields 27, 36 that contains the Mark.WW
     * and field 28, 35 that contains the Mark.BB.
     */
    @Test
    public void testSetup() {
        for (int i = 0; i < board.getDim() * board.getDim(); i++) {
            if (i == 27 || i == 36) {
                assertEquals(Mark.WW, board.getField(i));
            }
            if (i == 28 || i == 35) {
                assertEquals(Mark.BB, board.getField(i));
            }
            if (i != 28 && i != 35 && i != 27 && i != 36) {
                assertEquals(Mark.EMPTY, board.getField(i));
            }
        }
    }

    /**
     * Test if the field is EMPTY, if no mark was placed on it
     * and if the field is not 27, 28, 35, 36. Checks the method
     * isEmptyField(int index).
     */
    @Test
    public void testIsEmptyFieldIndex() {
        board.setField(1, Mark.WW);
        assertFalse(board.isEmptyField(1));
        assertTrue(board.isEmptyField(0));
        board.setField(15, Mark.BB);
        assertFalse(board.isEmptyField(15));
        assertTrue(board.isEmptyField(7));
        board.setField(20, Mark.BB);
        assertFalse(board.isEmptyField(20));
        board.setField(3, Mark.WW);
        assertFalse(board.isEmptyField(3));
        assertTrue(board.isEmptyField(8));
    }

    /**
     * Test if the board is full if all fields are occupied
     * by either Mark.WW or Mark.BB. Tests the method isFull().
     */
    @Test
    public void testIsFull() {
        assertFalse(board.isFull());
        for (int i = 2; i < board.getDim() * board.getDim(); i++) {
            board.setField(i, Mark.BB);
        }
        assertFalse(board.isFull());

        board.setField(0, Mark.BB);
        board.setField(1, Mark.WW);
        assertTrue(board.isFull());
    }

    /**
     * Test if the method index(int row, int col) returns the
     * index belonging to that field, given that the row >= 0 && row < DIM
     * and col >= 0 && col < DIM. If an invalid row or col is provided the method
     * should return -1.
     */
    @Test
    public void getIndex() {
        assertEquals(0, board.index(0, 0));
        assertEquals(1, board.index(0, 1));
        assertEquals(63, board.index(7, 7));
        for (int i = 0; i < board.getDim(); i++) {
            for (int j = 0; j < board.getDim(); j++) {
                assertEquals(i * board.getDim() + j, board.index(i, j));
            }
        }
    }

    /**
     * Test if the method getField(int i) returns the Mark belonging
     * to that field, given that i is a valid index; i >= 0 && i < 64.
     */
    @Test
    public void testGetField() {
        board.setField(10, Mark.BB);
        assertEquals(Mark.BB, board.getField(10));
        board.setField(20, Mark.WW);
        assertEquals(Mark.WW, board.getField(20));
        board.setField(30, Mark.BB);
        assertEquals(Mark.BB, board.getField(30));
        board.setField(40, Mark.WW);
        assertEquals(Mark.WW, board.getField(40));
        assertEquals(Mark.EMPTY, board.getField(0));
        assertNull(board.getField(-1));
        assertNull(board.getField(64));
        assertNull(board.getField(-2));
        assertNull(board.getField(-3));
        assertNull(board.getField(65));
        assertNull(board.getField(-1));
        assertNull(board.getField(66));

    }

    /**
     * Test if the method getField(int row, int col) returns the Mark belonging
     * to that field, given that row >= 0 && row < DIM and col >= 0 && col < DIM.
     */
    @Test
    public void testGetFieldWithRowCol() {
        board.setField(0, Mark.BB);
        assertEquals(Mark.BB, board.getField(0, 0));
        board.setField(63, Mark.WW);
        assertEquals(Mark.WW, board.getField(7, 7));
        board.setField(24, Mark.BB);
        assertEquals(Mark.BB, board.getField(3, 0));
        board.setField(44, Mark.WW);
        assertEquals(Mark.WW, board.getField(5, 4));
        assertNull(board.getField(-1, -1));
        assertNull(board.getField(64, 64));
        assertNull(board.getField(-2, -2));
        assertNull(board.getField(-3, -3));
        assertNull(board.getField(65, 65));
        assertNull(board.getField(-1, -1));
        // to reset the board
        setUp();
        int row;
        int col;
        for (int i = 0; i < board.getDim() * board.getDim(); i++) {
            row = i / board.getDim();
            col = i % board.getDim();
            if (i != 28 && i != 35 && i != 27 && i != 36) {
                assertEquals(Mark.EMPTY, board.getField(row, col));

            }
        }
    }

    /**
     * Test the method gamePossible(). If there are valid moves
     * for Mark.WW or Mark.BB then the method should return true,
     * otherwise it returns false.
     */
    @Test
    public void testGamePossible() {
        // at the beginning of the game there are possible moves
        assertTrue(board.gamePossible());

        board.setField(36, Mark.BB);
        board.setField(27, Mark.BB);
        // the board now is occupied by only one mark so no possible moves
        assertFalse(board.gamePossible());

        board.setField(37, Mark.WW);
        assertTrue(board.gamePossible());

        setUp();
        for (int i = 0; i < 40; i++) {
            board.setField(i, Mark.BB);
        }
        assertFalse(board.gamePossible());

    }

    /**
     * Tests if the game over prompt is correct, when the board is full.
     */
    @Test
    public void testGameOverFullBoard() {
        assertFalse(board.gameOver());
        /* Test for game over with full board (half board for each player, like this
         B B B B B B B B
         B B B B B B B B
         B B B B B B B B
         B B B B B B B B
         W W W W W W W W
         W W W W W W W W
         W W W W W W W W
         W W W W W W W W
         */
        for (int i = 0; i < 32; i++) {
            board.setField(i, Mark.BB);
        }
        for (int i = 32; i < 64; i++) {
            board.setField(i, Mark.WW);
        }
        assertTrue(board.gameOver());
    }

    /**
     * Tests if the game over prompt is correct
     * when both players have no valid moves to play.
     */
    @Test
    public void testGameOverNoMoreMoves() {
        /*
         Making the board such that it is not full
         but player 2 has no valid moves, like this
         - - - - - - - -
         - - - - - - - -
         - - - - B - - -
         - - - B B B - -
         - - B B B B B -
         - - - B B B - -
         - - - - B - - -
         - - - - - - - -
         This board is also present in our test plan.
        */
        assertFalse(board.gameOver());
        board.setField(20, Mark.BB);
        for (int i = 27; i <= 29; i++) {
            board.setField(i, Mark.BB);
        }
        for (int i = 34; i <= 38; i++) {
            board.setField(i, Mark.BB);
        }
        for (int i = 43; i <= 45; i++) {
            board.setField(i, Mark.BB);
        }
        board.setField(52, Mark.BB);
        assertTrue(board.calculateValidMoves(Mark.WW).isEmpty());
        assertTrue(board.calculateValidMoves(Mark.BB).isEmpty());
        assertTrue(board.gameOver());

        setUp();

    }


    /**
     * Test if the method countMarker(Mark m)
     * counts correctly the pieces of this mark on the board.
     */
    @Test
    public void testCountMarker() {
        // at the start of the game only 2 Mark.BB are on the board.
        assertEquals(2, board.countMarker(Mark.BB));

        // the board if full of Mark.BB, so it should be equal to 64
        for (int i = 0; i < board.getDim() * board.getDim(); i++) {
            board.setField(i, Mark.BB);
        }
        assertEquals(64, board.countMarker(Mark.BB));

        setUp();

        for (int i = 0; i < 32; i++) {
            board.setField(i, Mark.BB);
        }
        for (int i = 32; i < 64; i++) {
            board.setField(i, Mark.WW);
        }

        assertEquals(32, board.countMarker(Mark.WW));
        assertEquals(32, board.countMarker(Mark.BB));

        //if the board is empty then the countMarker() should return 0
        for (int i = 0; i < board.getDim() * board.getDim(); i++) {
            board.setField(i, Mark.EMPTY);
        }
        assertEquals(0, board.countMarker(Mark.WW));
        assertEquals(0, board.countMarker(Mark.BB));

    }

    /**
     * Tests the method isWinner(Mark m).
     * Check if the method returns true if m
     * is the winner (has more pieces on the table)
     * otherwise it should return false.
     */
    @Test
    public void testIsWinner() {

        for (int i = 0; i < board.getDim() * board.getDim(); i++) {
            board.setField(i, Mark.BB);
        }
        assertTrue(board.isWinner(Mark.BB));
        assertFalse(board.isWinner(Mark.WW));

        for (int i = 0; i < 40; i++) {
            board.setField(i, Mark.WW);
        }
        for (int i = 40; i < 64; i++) {
            board.setField(i, Mark.BB);
        }
        assertTrue(board.isWinner(Mark.WW));
        assertFalse(board.isWinner(Mark.BB));

    }


    /**
     * Test the method hasWinner().
     * It should return true if either Mark.BB
     * or Mark.WW won, else it is a draw and returns false.
     */
    @Test
    public void testHasWinner() {
        for (int i = 0; i < board.getDim() * board.getDim(); i++) {
            board.setField(i, Mark.WW);

        }
        assertTrue(board.hasWinner());
        setUp();

        for (int i = 0; i < board.getDim() * board.getDim() / 2; i++) {
            board.setField(i, Mark.WW);
        }
        for (int i = board.getDim() * board.getDim() / 2;
             i < board.getDim() * board.getDim(); i++) {
            board.setField(i, Mark.BB);
        }
        // there are 32 of WW and 32 of BB, so it is a draw
        assertFalse(board.hasWinner());

    }


    /**
     * Test if the method calculateValidMove(Mark m) returns a map that has as keys
     * only the valid moves.
     * A move is valid only if the current mark is placed on an empty field that is
     * adjacent to an opponent's mark, such that there is a mark of the same color on the row,
     * diag or col and there are pieces of the opponent's mark in between those two current marks.
     */
    @Test
    public void testCalculateValidMove() {
        assertTrue(board.calculateValidMoves(Mark.WW).containsKey(20));
        assertTrue(board.calculateValidMoves(Mark.WW).containsKey(29));
        assertTrue(board.calculateValidMoves(Mark.WW).containsKey(43));
        assertTrue(board.calculateValidMoves(Mark.WW).containsKey(34));
        assertFalse(board.calculateValidMoves(Mark.WW).containsKey(45));
        // at the beginning of the game there are always valid moves
        assertTrue(board.calculateValidMoves(Mark.BB).size() > 0);

        assertTrue(board.calculateValidMoves(Mark.BB).containsKey(19));
        assertTrue(board.calculateValidMoves(Mark.BB).containsKey(44));
        assertTrue(board.calculateValidMoves(Mark.BB).containsKey(26));
        assertTrue(board.calculateValidMoves(Mark.BB).containsKey(37));
        assertFalse(board.calculateValidMoves(Mark.BB).containsKey(50));

        // if the corner is occupied by a mark, then the neighbours will not be
        // valid moves for the other mark
        board.setField(7, Mark.BB);
        assertFalse(board.calculateValidMoves(Mark.WW).containsKey(6));
        assertFalse(board.calculateValidMoves(Mark.WW).containsKey(14));
        assertFalse(board.calculateValidMoves(Mark.WW).containsKey(15));

        board.setField(0, Mark.WW);
        assertFalse(board.calculateValidMoves(Mark.BB).containsKey(1));
        assertFalse(board.calculateValidMoves(Mark.BB).containsKey(9));
        assertFalse(board.calculateValidMoves(Mark.BB).containsKey(8));

        board.setField(56, Mark.BB);
        assertFalse(board.calculateValidMoves(Mark.WW).containsKey(48));
        assertFalse(board.calculateValidMoves(Mark.WW).containsKey(49));
        assertFalse(board.calculateValidMoves(Mark.WW).containsKey(57));

        board.setField(63, Mark.WW);
        assertFalse(board.calculateValidMoves(Mark.BB).containsKey(55));
        assertFalse(board.calculateValidMoves(Mark.BB).containsKey(54));
        assertFalse(board.calculateValidMoves(Mark.BB).containsKey(62));

        // same goes with a mark that is not placed in the corner but either
        // on row 0,7 or col 0,7
        board.setField(3, Mark.WW);
        assertFalse(board.calculateValidMoves(Mark.BB).containsKey(11));
        board.setField(2, Mark.BB);
        assertTrue(board.calculateValidMoves(Mark.BB).containsKey(4));

        // reset the board
        setUp();

        // 9 and 12 have in between marks of the other color
        // so 9 is a valid move, check in a row
        board.setField(10, Mark.BB);
        board.setField(11, Mark.BB);
        board.setField(12, Mark.WW);
        assertTrue(board.calculateValidMoves(Mark.WW).containsKey(9));
        // now there is an empty mark between those 2 white marks, so
        // field 9 is not valid anymore
        board.setField(11, Mark.EMPTY);
        assertFalse(board.calculateValidMoves(Mark.WW).containsKey(9));

        // on a col between field 14 and 46 there are only white marks
        // so 14 is a valid move
        board.setField(22, Mark.WW);
        board.setField(30, Mark.WW);
        board.setField(38, Mark.WW);
        board.setField(46, Mark.BB);
        assertTrue(board.calculateValidMoves(Mark.BB).containsKey(14));

        // now that the next mark on col 22 is of the same color as mark
        // 14, field 14 is not a valid move anymore
        board.setField(22, Mark.BB);
        assertFalse(board.calculateValidMoves(Mark.BB).containsKey(12));
        // now that the mark 46 is white, there are no valid moves
        board.setField(22, Mark.WW);
        board.setField(46, Mark.WW);
        assertFalse(board.calculateValidMoves(Mark.BB).containsKey(12));

        // reset the board
        setUp();

        // check diagonal up-right
        board.setField(42, Mark.WW);
        // from field 21 until field 42 on diagonal are only black marks
        // so field 21 should be a valid field for mark white
        assertTrue(board.calculateValidMoves(Mark.WW).containsKey(21));
        assertFalse(board.calculateValidMoves(Mark.WW).containsKey(14));

        // check diagonal up-left
        board.setField(45, Mark.BB);
        assertTrue(board.calculateValidMoves(Mark.BB).containsKey(18));
        assertFalse(board.calculateValidMoves(Mark.BB).containsKey(27));
        assertFalse(board.calculateValidMoves(Mark.BB).containsKey(9));
        // reset
        setUp();

        // check diagonal down-right
        board.setField(18, Mark.BB);
        assertTrue(board.calculateValidMoves(Mark.BB).containsKey(45));
        assertFalse(board.calculateValidMoves(Mark.BB).containsKey(63));

        // check diagonal down-left
        board.setField(21, Mark.WW);
        assertTrue(board.calculateValidMoves(Mark.WW).containsKey(42));
        assertFalse(board.calculateValidMoves(Mark.WW).containsKey(35));

    }


    /**
     * Test if a mark has another mark of the same color on a row, such that they
     * have in between only opponent's pieces. CheckRow is called inside calculateValidMoves
     * that takes care that the argument passed to checkRow are always the fields that have an
     * opponent mark as a neighbour.
     */
    @Test
    public void testCheckRow() {

        assertEquals(1, board.checkRow(26, 27, Mark.BB).size());
        assertTrue(board.checkRow(26, 27, Mark.BB).contains(28));
        assertEquals(1, board.checkRow(37, 36, Mark.BB).size());
        assertTrue(board.checkRow(37, 36, Mark.BB).contains(35));
        assertFalse(board.checkRow(2, 3, Mark.WW).contains(4));
        assertTrue(board.calculateValidMoves(Mark.BB).get(26).contains(28)
                && board.checkRow(26, 27, Mark.BB).contains(28));

    }


    /**
     * Test if a mark has another mark of the same color on a col, such that they
     * have in between only opponent's pieces. CheckCol is called inside calculateValidMoves
     * that takes care that the argument passed to checkCol are always the fields that have an
     * opponent mark as a neighbour.
     */
    @Test
    public void testCheckColumn() {
        board.setField(17, Mark.BB);
        board.setField(25, Mark.WW);
        board.setField(33, Mark.WW);
        assertEquals(1, board.checkColumn(41, 33, Mark.BB).size());
        assertTrue(board.checkColumn(41, 33, Mark.BB).contains(17));

        assertTrue(board.calculateValidMoves(Mark.BB).get(41).contains(17)
                && board.checkColumn(41, 33, Mark.BB).contains(17));
        assertFalse(board.checkColumn(0, 8, Mark.WW).contains(16));


    }

    /**
     * Test if a mark has another mark of the same color on a diagonal, such that they
     * have in between only opponent's pieces. CheckDiagonal is called inside calculateValidMoves
     * that takes care that the argument passed to checkDiagonal are always the fields that have an
     * opponent mark as a neighbour.
     */
    @Test
    public void testCheckDiagonal() {
        board.setField(21, Mark.WW);
        assertEquals(1, board.checkDiagonal(42, 35, Mark.WW).size());
        assertTrue(board.checkDiagonal(42, 35, Mark.BB).contains(28));

        assertTrue(board.calculateValidMoves(Mark.WW).get(42).contains(21)
                && board.checkDiagonal(42, 35, Mark.WW).contains(21));


        board.setField(45, Mark.BB);
        assertEquals(1, board.checkDiagonal(18, 27, Mark.BB).size());
        assertTrue(board.checkDiagonal(18, 27, Mark.WW).contains(36));

        assertTrue(board.calculateValidMoves(Mark.BB).get(18).contains(45)
                && board.checkDiagonal(18, 27, Mark.BB).contains(45));

    }


    /**
     * Test the method getAdjacentEnemies(Mark m)
     * to see if it returns a map that contains as key
     * the possible field of the current mark mapped to a list
     * of all the adjacent marks of the opposite color.
     */
    @Test
    public void getAdjacentEnemy() {
        assertTrue(board.getAdjacentEnemies(Mark.WW).
                containsKey(19));
        assertTrue(board.getAdjacentEnemies(Mark.WW).
                containsKey(20));
        assertTrue(board.getAdjacentEnemies(Mark.WW).
                containsKey(21));
        assertTrue(board.getAdjacentEnemies(Mark.WW).
                containsKey(29));
        assertTrue(board.getAdjacentEnemies(Mark.WW).
                containsKey(26));
        assertTrue(board.getAdjacentEnemies(Mark.WW).
                containsKey(37));
        assertTrue(board.getAdjacentEnemies(Mark.WW).
                containsKey(34));
        assertTrue(board.getAdjacentEnemies(Mark.WW).
                containsKey(42));
        assertTrue(board.getAdjacentEnemies(Mark.WW).
                containsKey(43));
        assertTrue(board.getAdjacentEnemies(Mark.WW).
                containsKey(44));
        assertTrue(board.getAdjacentEnemies(Mark.WW).
                containsValue(new ArrayList<>(List.of(28))));
        assertTrue(board.getAdjacentEnemies(Mark.WW).
                containsValue(new ArrayList<>(List.of(35))));

        List<Integer> list1 = new ArrayList<>(Arrays.asList(19, 29, 21, 20, 37));
        for (Integer i : list1) {
            assertEquals(new ArrayList<>(List.of(28)),
                    board.getAdjacentEnemies(Mark.WW).get(i));
        }

        list1 = new ArrayList<>(Arrays.asList(26, 34, 42, 43, 44));
        for (Integer i : list1) {
            assertEquals(new ArrayList<>(List.of(35)),
                    board.getAdjacentEnemies(Mark.WW).get(i));
        }

        assertTrue(board.getAdjacentEnemies(Mark.BB).
                containsKey(18));
        assertTrue(board.getAdjacentEnemies(Mark.BB).
                containsKey(19));
        assertTrue(board.getAdjacentEnemies(Mark.BB).
                containsKey(20));
        assertTrue(board.getAdjacentEnemies(Mark.BB).
                containsKey(26));
        assertTrue(board.getAdjacentEnemies(Mark.BB).
                containsKey(34));
        assertTrue(board.getAdjacentEnemies(Mark.BB).
                containsKey(43));
        assertTrue(board.getAdjacentEnemies(Mark.BB).
                containsKey(44));
        assertTrue(board.getAdjacentEnemies(Mark.BB).
                containsKey(45));
        assertTrue(board.getAdjacentEnemies(Mark.BB).
                containsKey(37));
        assertTrue(board.getAdjacentEnemies(Mark.BB).
                containsKey(29));
        assertTrue(board.getAdjacentEnemies(Mark.BB).
                containsValue(new ArrayList<>(List.of(27))));
        assertTrue(board.getAdjacentEnemies(Mark.BB).
                containsValue(new ArrayList<>(List.of(36))));
        list1 = new ArrayList<>(Arrays.asList(18, 19, 20, 26, 34));
        for (Integer i : list1) {
            assertEquals(new ArrayList<>(List.of(27)),
                    board.getAdjacentEnemies(Mark.BB).get(i));
        }

        list1 = new ArrayList<>(Arrays.asList(43, 44, 45, 37, 29));
        for (Integer i : list1) {
            assertEquals(new ArrayList<>(List.of(36)),
                    board.getAdjacentEnemies(Mark.BB).get(i));
        }


        // for testing the corners
        board.setField(7, Mark.WW);
        assertTrue(board.getAdjacentEnemies(Mark.BB).get(6).contains(7));
        assertTrue(board.getAdjacentEnemies(Mark.BB).get(14).contains(7));
        assertTrue(board.getAdjacentEnemies(Mark.BB).get(15).contains(7));
        assertFalse(board.getAdjacentEnemies(Mark.BB).get(0).contains(7));
        assertFalse(board.getAdjacentEnemies(Mark.BB).get(63).contains(7));

        board.setField(0, Mark.BB);
        assertTrue(board.getAdjacentEnemies(Mark.WW).get(1).contains(0));
        assertTrue(board.getAdjacentEnemies(Mark.WW).get(9).contains(0));
        assertTrue(board.getAdjacentEnemies(Mark.WW).get(8).contains(0));
        assertFalse(board.getAdjacentEnemies(Mark.WW).get(50).contains(0));
        assertFalse(board.getAdjacentEnemies(Mark.WW).get(63).contains(0));

        board.setField(56, Mark.WW);
        assertTrue(board.getAdjacentEnemies(Mark.BB).get(48).contains(56));
        assertTrue(board.getAdjacentEnemies(Mark.BB).get(49).contains(56));
        assertTrue(board.getAdjacentEnemies(Mark.BB).get(57).contains(56));
        assertFalse(board.getAdjacentEnemies(Mark.BB).get(50).contains(56));
        assertFalse(board.getAdjacentEnemies(Mark.BB).get(63).contains(56));

        board.setField(63, Mark.BB);
        assertTrue(board.getAdjacentEnemies(Mark.WW).get(62).contains(63));
        assertTrue(board.getAdjacentEnemies(Mark.WW).get(54).contains(63));
        assertTrue(board.getAdjacentEnemies(Mark.WW).get(55).contains(63));
        assertFalse(board.getAdjacentEnemies(Mark.WW).get(51).contains(63));
        assertFalse(board.getAdjacentEnemies(Mark.WW).get(50).contains(63));


        // test if on the board there are only Mark.WW then Mark.WW will not have
        // any neighboring opponents
        setUp();
        board.setField(28, Mark.WW);
        board.setField(35, Mark.WW);
        assertTrue(board.getAdjacentEnemies(Mark.WW).size() != 0);

    }


}

