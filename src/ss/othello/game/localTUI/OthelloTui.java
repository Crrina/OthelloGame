package ss.othello.game.localTUI;

import ss.othello.game.ai.ComputerPlayer;
import ss.othello.game.ai.NaiveStrategy;
import ss.othello.game.ai.SmartStrategy;
import ss.othello.game.model.Mark;
import ss.othello.game.model.Move;
import ss.othello.game.model.OthelloGame;
import ss.othello.game.model.Player;

import java.util.Scanner;

/**
 * This class enables 2 players to play Othello locally, pass-n-play style.
 * Both players must enter their names and the game will begin.
 * After it ends, you will be asked if you would like to play again.
 */
public class OthelloTui {


    private static Scanner scanner = new Scanner(System.in);
    private Player player1;
    private Player player2;

    private OthelloGame game;


    /**
     * Starts a new instance of the Tui.
     *
     * @param player1 Player one
     * @param player2 Player two
     */
    /*@
        requires player1 != null && player2 != null;
        ensures this.player1.equals(player1) && this.player2.equals(player2);
    */
    public OthelloTui(Player player1, Player player2) {
        this.player1 = player1;
        this.player2 = player2;
    }

    /**
     * The main application which runs the game.
     *
     * @param args command line arguments
     */
    public static void main(String[] args) {
        boolean want = true;
        while (want) {
            OthelloTui tui = askName();
            tui.run();
            want = askAnotherGame() ? true : false;
        }
        System.out.println("Game finished, bye!");


    }

    /**
     * The method which asks for 2 players and starts a new Tui accordingly.
     * If -N is entered as the name, then the player plays with the NaiveAi.
     * if -S in entered as the name, then the player plays with the SmartAi.
     *
     * @return new Tui instance with player 1 and player 2.
     */
    /*@
        ensures \result != null;
        ensures \result == new OthelloTui(player1, player2);
    */
    private static OthelloTui askName() {
        System.out.println("Welcome to Othello!");
        System.out.println("Enter the name of the first player: ");
        String player1 = scanner.nextLine();
        System.out.println("Enter the name of the second player: ");
        String player2 = scanner.nextLine();
        if (player1.equals("-N") && player2.equals("-S")) {
            return new OthelloTui(new ComputerPlayer(Mark.BB, new NaiveStrategy()),
                    new ComputerPlayer(Mark.WW, new SmartStrategy()));
        } else if (player1.equals("-S") && player2.equals("-N")) {
            return new OthelloTui(new ComputerPlayer(Mark.BB, new SmartStrategy()),
                    new ComputerPlayer(Mark.WW, new NaiveStrategy()));
        } else if (player1.equals("-N") && player2.equals("-N")) {
            return new OthelloTui(new ComputerPlayer(Mark.BB, new NaiveStrategy()),
                    new ComputerPlayer(Mark.WW, new NaiveStrategy()));
        } else if (player1.equals("-N")) {
            return new OthelloTui(new ComputerPlayer(Mark.BB, new NaiveStrategy()),
                    new HumanPlayer(player2));
        } else if (player2.equals("-N")) {
            return new OthelloTui(new HumanPlayer(player1),
                    new ComputerPlayer(Mark.WW, new NaiveStrategy()));
        } else if (player1.equals("-S") && player2.equals("-S")) {
            return new OthelloTui(new ComputerPlayer(Mark.BB, new SmartStrategy()),
                    new ComputerPlayer(Mark.WW, new SmartStrategy()));
        } else if (player1.equals("-S")) {
            return new OthelloTui(new ComputerPlayer(Mark.BB, new SmartStrategy()),
                    new HumanPlayer(player2));
        } else if (player2.equals("-S")) {
            return new OthelloTui(new HumanPlayer(player1), new ComputerPlayer(Mark.WW,
                    new SmartStrategy()));
        } else {
            return new OthelloTui(new HumanPlayer(player1), new HumanPlayer(player2));
        }

    }


    /**
     * Asks the users if they want to play again.
     *
     * @return true if players want to play another game, false otherwise
     */
    private static boolean askAnotherGame() {
        boolean wait = false;
        while (!wait) {
            System.out.println(
                    "Want to play another game?" +
                            "\nEnter yes to play" +
                            "\nEnter no to quit");
            String input = scanner.nextLine();
            if (input.equalsIgnoreCase("yes")) {
                return true;
            }
            if (input.equalsIgnoreCase("no")) {
                wait = true;
            }
        }
        return false;
    }

    /**
     * Runs the Othello game.
     * Until the game is not over the player will be asked to
     * input moves and the validity of the move will be checked before performing it.
     * When the game is over it will print the winner, if there is one.
     */
    /*@
        ensures this.game == new OthelloGame(this.player1, this.player2);
    */
    public void run() {
        game = new OthelloGame(player1, player2);
        while (!game.isGameover()) {
            System.out.println(game.toString());
            //get the current player
            Player player = game.getTurn();
            if (player instanceof HumanPlayer) {
                Move move = ((HumanPlayer) player).determineMove(game);
                if (move != null) {
                    game.doMove(move);
                } else {
                    int current = game.getCurrent() == 0 ? 1 : 0;
                    game.setCurrent(current);
                }
            }
            if (player instanceof ComputerPlayer) {
                Move move = ((ComputerPlayer) player).determineMove(game);
                if (move != null) {
                    game.doMove(move);
                    System.out.println(player + " moved " + move.getField());
                } else {
                    int current = game.getCurrent() == 0 ? 1 : 0;
                    game.setCurrent(current);
                }
            }
        }
        if (game.getBoard().hasWinner()) {
            System.out.println(game.getBoard());
            System.out.println("The winner of the game is: " + game.getWinner());

        } else {
            System.out.println("There is a draw ");
        }
        System.out.println(Mark.BB + ": " + game.getBoard().countMarker(Mark.BB));
        System.out.println(Mark.WW + ": " + game.getBoard().countMarker(Mark.WW));
    }


}
