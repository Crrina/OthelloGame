package ss.othello.networking.server;

import ss.othello.exceptions.InvalidPortNumber;
import ss.othello.networking.ClassFactory;
import ss.othello.networking.Factory;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.InputMismatchException;


/**
 * Class ServerStart that is responsible for starting the server.
 * The user is asked to input a port number between 0 and 65535
 * and then the Server class is started. ServerStart reads the input
 * in a while loop and stops if 'QUIT' was given.
 */
public class ServerStart {

    /**
     * The main method that asks for the port number until a valid one was given
     * and then starts the Server. If a port number that is in use is given,
     * then the user will be asked to re-enter another port number.
     *
     * @param args the args of the main method, not used in this case.
     */
    public static void main(String[] args) {
        Factory factory = new ClassFactory();
        int port;
        BufferedReader reader = new BufferedReader(new InputStreamReader(System.in));
        while (true) {
            try {
                System.out.println("Input a valid port number (0 - 65535)");
                String line = reader.readLine();
                port = Integer.parseInt(line);
                if (port > 65535 || port < 0) {
                    throw new InvalidPortNumber("You need to enter a valid port number!");
                } else {
                    break;
                }
            } catch (InvalidPortNumber e) {
                System.err.println(e.getMessage());
            } catch (NumberFormatException | InputMismatchException e) {
                System.err.println("You need to enter a number!");
            } catch (IOException e) {
                System.err.println("IO exception occurred!");
            }
        }
        Server server = factory.makeServer(port);
        if (server.isPortIsFree()) {
            server.start();
        } else {
            String[] wrong = {"Already in use"};
            main(wrong);
        }
        String line;
        try {
            while ((line = reader.readLine()) != null) {
                if (line.equalsIgnoreCase("QUIT")) {
                    server.stop();
                    System.exit(0);
                    break;
                }
            }
        } catch (IOException e) {
            System.err.println("An IO Exception has occurred!");
        }
    }
}




