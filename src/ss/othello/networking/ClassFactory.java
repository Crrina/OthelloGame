package ss.othello.networking;

import ss.othello.networking.client.Client;
import ss.othello.networking.server.Server;

/**
 * This class is responsible for creating new servers and clients.
 */
public class ClassFactory implements Factory {


    /**
     * Makes a new server instance.
     *
     * @param port port for server to listen on
     * @return Server created
     */
    @Override
    public Server makeServer(int port) {
        return new Server(port);
    }

    /**
     * Makes a new Client instance.
     *
     * @return Client created
     */
    @Override
    public Client makeClient() {
        return new Client();
    }
}
