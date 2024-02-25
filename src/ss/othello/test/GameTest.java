package ss.othello.test;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import ss.othello.game.ai.ComputerPlayer;
import ss.othello.game.ai.NaiveStrategy;
import ss.othello.game.localTUI.HumanPlayer;
import ss.othello.game.model.*;

import java.util.Random;

import static org.junit.jupiter.api.Assertions.*;


/**
 * This class includes tests for the methods in Game
 * including logic such as determining game over, changing the turn
 * and flipping markers.
 */
class GameTest {
    OthelloGame game;
    Player p1;
    Player p2;

    /**
     * Set up before each test.
     */
    @BeforeEach
    public void setUp() {
        p1 = new HumanPlayer("player 1");
        p2 = new HumanPlayer("player 2");
        game = new OthelloGame(p1, p2);
    }

    /**
     * Tests the game over method in game
     * when the board is full.
     */
    @Test
    public void testGameOverFullBoard() {
        p1 = new ComputerPlayer(Mark.BB, new NaiveStrategy());
        p2 = new ComputerPlayer(Mark.WW, new NaiveStrategy());
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
        assertFalse(game.isGameover());
        // Filling board up randomly, no empty fields
        for (int i = 0; i < game.getBoard().getDim() * game.getBoard().getDim(); i++) {
            if (i < 32) {
                game.getBoard().setField(i, Mark.BB);
            } else {
                game.getBoard().setField(i, Mark.WW);
            }
        }
        assertTrue(game.isGameover());
    }

    /**
     * Tests the game over method in game
     * when there are no more valid moves for both players.
     */
    @Test
    public void testGameOverNoMoreMoves() {
        assertFalse(game.isGameover());
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
         This is also present in our test plan.
        */
        Board board = game.getBoard();
        Mark b = Mark.BB;
        Mark w = Mark.WW;
        game.doMove(new OthelloMove(b, 37, board));
        game.doMove(new OthelloMove(w, 43, board));
        game.doMove(new OthelloMove(b, 34, board));
        game.doMove(new OthelloMove(w, 29, board));
        game.doMove(new OthelloMove(b, 20, board));
        game.doMove(new OthelloMove(w, 45, board));
        game.doMove(new OthelloMove(b, 38, board));
        game.doMove(new OthelloMove(w, 44, board));
        game.doMove(new OthelloMove(b, 52, board));
        assertTrue(game.isGameover());
    }


    /**
     * Test for the method that checks if a move is valid.
     */
    @Test
    public void testValidMove() {
        OthelloMove move = new OthelloMove(Mark.BB, 1, game.getBoard());
        assertFalse(game.isValidMove(move));
        move = new OthelloMove(Mark.BB, 19, game.getBoard());
        assertTrue(game.isValidMove(move));
        move = new OthelloMove(Mark.BB, 38, game.getBoard());
        assertFalse(game.isValidMove(move));
        move = new OthelloMove(Mark.BB, 37, game.getBoard());
        assertTrue(game.isValidMove(move));
        move = new OthelloMove(Mark.BB, 0, game.getBoard());
        assertFalse(game.isValidMove(move));
    }

    /**
     * Tests that the get valid moves method
     * returns a list of all valid moves.
     */
    @Test
    public void testAllValidMoves() {
        for (Move validMove : game.getValidMoves()) {
            assertTrue(game.isValidMove(validMove));
        }
    }

    /**
     * Tests that setting current changes
     * the player whose turn it is.
     */
    @Test
    public void testSetCurrent() {
        assertEquals(game.getCurrent(), 0);
        assertEquals(game.getTurn(), p1);
        game.setCurrent(1);
        assertEquals(game.getCurrent(), 1);
        assertEquals(game.getTurn(), p2);
    }

    /**
     * Test for the method to correctly return
     * the player whose turn it is currently.
     */
    @Test
    public void testTurn() {
        assertEquals(0, game.getCurrent());
        assertEquals(p1, game.getTurn());
        OthelloMove move = new OthelloMove(Mark.BB, 19, game.getBoard());
        game.doMove(move);
        assertEquals(1, game.getCurrent());
        assertEquals(p2, game.getTurn());
    }

    /**
     * Tests that doing a move automatically
     * sets current to the other value and changes
     * the turn.
     */
    @Test
    public void testChangeTurn() {
        assertEquals(game.getCurrent(), 0);
        assertEquals(game.getTurn(), p1);
        game.doMove(new OthelloMove(Mark.BB, 19, game.getBoard()));
        assertEquals(game.getCurrent(), 1);
        assertEquals(game.getTurn(), p2);
        game.doMove(new OthelloMove(Mark.WW, 20, game.getBoard()));
        assertEquals(game.getCurrent(), 0);
        assertEquals(game.getTurn(), p1);
    }

    /**
     * Tests that the board is set up correctly
     * according to the rules of Othello.
     */
    @Test
    public void testBoardGameSetup() {
        int totalField = (int) Math.pow(game.getBoard().getDim(), 2);
        for (int i = 0; i < totalField; i++) {
            Mark current = game.getBoard().getField(i);
            if (i == 27 || i == 36) {
                assertEquals(Mark.WW, current);
            } else if (i == 28 || i == 35) {
                assertEquals(Mark.BB, current);
            } else {
                assertEquals(Mark.EMPTY, current);
            }
        }
    }

    /**
     * Tests if the opponent markers are being flipped correctly.
     */
    @Test
    public void testFlip() {
        int totalField = (int) Math.pow(game.getBoard().getDim(), 2);
        testBoardGameSetup();
        OthelloMove move = new OthelloMove(Mark.BB, 19, game.getBoard());
        game.doMove(move);
        /*
         - - - - - - - -
         - - - - - - - -
         - - - B - - - -
         - - - B B - - -
         - - - B W - - -
         - - - - - - - -
         - - - - - - - -
         - - - - - - - -
         */
        for (int i = 0; i < totalField; i++) {
            Mark current = game.getBoard().getField(i);
            if (i == 36) {
                assertEquals(Mark.WW, current);
            } else if (i == 28 || i == 35 || i == 19 || i == 27) {
                assertEquals(Mark.BB, current);
            } else {
                assertEquals(Mark.EMPTY, current);
            }
        }
        move = new OthelloMove(Mark.WW, 20, game.getBoard());
        game.doMove(move);
        /*
         - - - - - - - -
         - - - - - - - -
         - - - B W - - -
         - - - B W - - -
         - - - B W - - -
         - - - - - - - -
         - - - - - - - -
         - - - - - - - -
         */
        for (int i = 0; i < totalField; i++) {
            Mark current = game.getBoard().getField(i);
            if (i == 36 || i == 28 || i == 20) {
                assertEquals(Mark.WW, current);
            } else if (i == 35 || i == 19 || i == 27) {
                assertEquals(Mark.BB, current);
            } else {
                assertEquals(Mark.EMPTY, current);
            }
        }
        move = new OthelloMove(Mark.BB, 21, game.getBoard());
        game.doMove(move);
        /*
         - - - - - - - -
         - - - - - - - -
         - - - B B B - -
         - - - B B - - -
         - - - B W - - -
         - - - - - - - -
         - - - - - - - -
         - - - - - - - -
         */
        for (int i = 0; i < totalField; i++) {
            Mark current = game.getBoard().getField(i);
            if (i == 36) {
                assertEquals(Mark.WW, current);
            } else if (i == 28 || i == 35 || i == 19 || i == 27 || i == 20 || i == 21) {
                assertEquals(Mark.BB, current);
            } else {
                assertEquals(Mark.EMPTY, current);
            }
        }
    }

    /**
     * Tests to see if the winner of a game is correctly returned.
     */
    @Test
    public void testGameWinner() {
        testGameOverNoMoreMoves(); // The game where all pieces are black
        assertEquals(p1, game.getWinner());
        game = new OthelloGame(p1, p2);
        Board board = game.getBoard();
        // Adding moves from a game where white wins (full board win), like this:
        /*
         B B B B W B B B
         B B B W W W W W
         B B W W W B W W
         B W B W B B W W
         B W W B W W B B
         B W B B B B B B
         W W W W W B B W
         W W W W W W B W
         */
        game.doMove(new OthelloMove(Mark.BB, 37, board));
        game.doMove(new OthelloMove(Mark.WW, 29, board));
        game.doMove(new OthelloMove(Mark.BB, 21, board));
        game.doMove(new OthelloMove(Mark.WW, 30, board));
        game.doMove(new OthelloMove(Mark.BB, 19, board));
        game.doMove(new OthelloMove(Mark.WW, 26, board));
        game.doMove(new OthelloMove(Mark.BB, 33, board));
        game.doMove(new OthelloMove(Mark.WW, 11, board));
        game.doMove(new OthelloMove(Mark.BB, 39, board));
        game.doMove(new OthelloMove(Mark.WW, 25, board));
        game.doMove(new OthelloMove(Mark.BB, 17, board));
        game.doMove(new OthelloMove(Mark.WW, 45, board));
        game.doMove(new OthelloMove(Mark.BB, 53, board));
        game.doMove(new OthelloMove(Mark.WW, 43, board));
        game.doMove(new OthelloMove(Mark.BB, 42, board));
        game.doMove(new OthelloMove(Mark.WW, 20, board));
        game.doMove(new OthelloMove(Mark.BB, 10, board));
        game.doMove(new OthelloMove(Mark.WW, 18, board));
        game.doMove(new OthelloMove(Mark.BB, 44, board));
        game.doMove(new OthelloMove(Mark.WW, 51, board));
        game.doMove(new OthelloMove(Mark.BB, 12, board));
        game.doMove(new OthelloMove(Mark.WW, 31, board));
        game.doMove(new OthelloMove(Mark.BB, 50, board));
        game.doMove(new OthelloMove(Mark.WW, 24, board));
        game.doMove(new OthelloMove(Mark.BB, 38, board));
        game.doMove(new OthelloMove(Mark.WW, 58, board));
        game.doMove(new OthelloMove(Mark.BB, 40, board));
        game.doMove(new OthelloMove(Mark.WW, 2, board));
        game.doMove(new OthelloMove(Mark.BB, 34, board));
        game.doMove(new OthelloMove(Mark.WW, 9, board));
        game.doMove(new OthelloMove(Mark.BB, 60, board));
        game.doMove(new OthelloMove(Mark.WW, 13, board));
        game.doMove(new OthelloMove(Mark.BB, 57, board));
        game.doMove(new OthelloMove(Mark.WW, 59, board));
        game.doMove(new OthelloMove(Mark.BB, 5, board));
        game.doMove(new OthelloMove(Mark.WW, 61, board));
        game.doMove(new OthelloMove(Mark.BB, 22, board));
        game.doMove(new OthelloMove(Mark.WW, 46, board));
        game.doMove(new OthelloMove(Mark.BB, 3, board));
        game.doMove(new OthelloMove(Mark.WW, 49, board));
        game.doMove(new OthelloMove(Mark.BB, 0, board));
        game.doMove(new OthelloMove(Mark.WW, 16, board));
        game.doMove(new OthelloMove(Mark.BB, 54, board));
        game.doMove(new OthelloMove(Mark.WW, 23, board));
        game.doMove(new OthelloMove(Mark.BB, 14, board));
        game.doMove(new OthelloMove(Mark.WW, 32, board));
        game.doMove(new OthelloMove(Mark.BB, 41, board));
        game.doMove(new OthelloMove(Mark.WW, 63, board));
        game.doMove(new OthelloMove(Mark.BB, 52, board));
        game.doMove(new OthelloMove(Mark.WW, 55, board));
        game.doMove(new OthelloMove(Mark.BB, 8, board));
        game.doMove(new OthelloMove(Mark.WW, 6, board));
        game.doMove(new OthelloMove(Mark.BB, 7, board));
        game.doMove(new OthelloMove(Mark.WW, 56, board));
        game.doMove(new OthelloMove(Mark.BB, 47, board));
        game.doMove(new OthelloMove(Mark.WW, 48, board));
        game.doMove(new OthelloMove(Mark.BB, 1, board));
        game.doMove(new OthelloMove(Mark.WW, 4, board));
        game.doMove(new OthelloMove(Mark.BB, 62, board));
        game.doMove(new OthelloMove(Mark.WW, 15, board));
        assertEquals(p2, game.getWinner());
        assertNotEquals(p1, game.getWinner());
        assertNotNull(game.getWinner());
    }

    /**
     * Tests to see if a game draw result is correctly reported.
     */
    @Test
    public void testDraw() {
        testGameOverFullBoard(); // the board where half the board was black and half white
        assertNull(game.getWinner());
    }

    /**
     * Tests a game from start to finish with
     * random valid moves (Naive bots).
     */
    @Test
    void randomGameFromNaiveBots() {
        Move move;
        p1 = new ComputerPlayer(Mark.BB, new NaiveStrategy());
        p2 = new ComputerPlayer(Mark.WW, new NaiveStrategy());
        int initial;
        game = new OthelloGame(p1, p2);
        while (!game.isGameover()) {
            if (!game.getValidMoves().isEmpty()) {
                move = ((ComputerPlayer) p1).determineMove(game);
                initial = game.getBoard().countMarker(Mark.BB);
                assertTrue(game.isValidMove(move));
                game.doMove(move);
                assertTrue(initial < game.getBoard().countMarker(Mark.BB));
            } else {
                game.setCurrent(1);
            }
            if (!game.getValidMoves().isEmpty()) {
                move = ((ComputerPlayer) p2).determineMove(game);
                initial = game.getBoard().countMarker(Mark.WW);
                assertTrue(game.isValidMove(move));
                game.doMove(move);
                assertTrue(initial < game.getBoard().countMarker(Mark.WW));
            } else {
                game.setCurrent(0);
            }
        }
        if (game.getBoard().countMarker(Mark.BB) >
                game.getBoard().countMarker(Mark.WW)) {
            assertEquals(game.getWinner(), p1);
        } else if (game.getBoard().countMarker(Mark.BB) <
                game.getBoard().countMarker(Mark.WW)) {
            assertEquals(game.getWinner(), p2);
        } else {
            assertTrue(!game.getBoard().hasWinner());
        }
    }


    /**
     * Tests a game from start to finish
     * with random moves (which can be invalid).
     */
    @Test
    void testTrueRandomMoves() {
        int counter = 0;
        Move move;
        p1 = new HumanPlayer("player 1");
        p2 = new HumanPlayer("player 2");
        int initial;
        game = new OthelloGame(p1, p2);
        while (!game.isGameover()) {
            while (!game.getBoard().calculateValidMoves(Mark.BB).isEmpty()) {
                move = new OthelloMove(Mark.BB, new Random().nextInt(game.getBoard().getDim() *
                        game.getBoard().getDim()), game.getBoard());
                initial = game.getBoard().countMarker(Mark.BB);
                if (game.isValidMove(move)) {
                    game.doMove(move);
                    assertTrue(initial < game.getBoard().countMarker(Mark.BB));
                    counter++;
                    break;
                } else {
                    assertFalse(game.isValidMove(move));
                }
            }
            if (counter != 1) {
                game.setCurrent(1);
            }
            while (!game.getBoard().calculateValidMoves(Mark.WW).isEmpty()) {
                move = new OthelloMove(Mark.WW, new Random().nextInt(game.getBoard().getDim() *
                        game.getBoard().getDim()), game.getBoard());
                initial = game.getBoard().countMarker(Mark.WW);
                if (game.isValidMove(move)) {
                    game.doMove(move);
                    assertTrue(initial < game.getBoard().countMarker(Mark.WW));
                    counter = 0;
                    break;
                } else {
                    assertFalse(game.isValidMove(move));
                }
            }
            if (counter != 0) {
                game.setCurrent(0);
            }
        }
        if (game.getBoard().countMarker(Mark.BB) >
                game.getBoard().countMarker(Mark.WW)) {
            assertEquals(game.getWinner(), p1);
        } else if (game.getBoard().countMarker(Mark.BB) <
                game.getBoard().countMarker(Mark.WW)) {
            assertEquals(game.getWinner(), p2);
        } else {
            assertFalse(game.getBoard().hasWinner());
        }
    }
}


