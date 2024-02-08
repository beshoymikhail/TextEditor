## Build the Docker Image
Run the following command in the directory containing your Dockerfile

```shell
docker build -t texteditor .
```

## Run the Docker Container
To run your Blazor app in a Docker container, use:

```shell
docker run -d -p 8080:80 --name texteditor texteditor
```
